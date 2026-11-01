/*
 * YouTube_Clean_response.js  —  v0.1 (experimental)
 *
 * Loon http-response script for https://youtubei.googleapis.com/youtubei/v1/*
 * (YouTube / YouTube Music iOS app, protobuf bodies, binary-body mode)
 *
 * SECURITY INVARIANTS (grep this file to check them):
 *   - No network access: no $httpClient / fetch / XMLHttpRequest / WebSocket
 *   - No storage: no $persistentStore / localStorage
 *   - No headers, cookies or tokens are read, written or logged
 *   - No eval / Function / dynamic code loading
 *   - Fail-open: on ANY error the original response is returned untouched
 *   - Edits are byte-splices: every field not explicitly changed stays byte-identical
 *   - The only I/O is reading $response body and calling $done()
 *
 * PROVENANCE OF FIELD NUMBERS
 *   Field numbers come from the protobuf schema embedded in Maasea/sgmodule
 *   (Apache-2.0, build 2026/7/19 16:16:39). They were checked by reading,
 *   NOT by testing against a live YouTube app. See the "VERIFIED" tags below.
 *
 * Positional $argument order (same as the original plugin):
 *   blockUpload, blockShorts, blockImmersive, captionLang, debug
 */

"use strict";

/* ------------------------------------------------------------------ */
/* 1. protobuf wire-format helpers (no schema, no re-encoding)         */
/* ------------------------------------------------------------------ */

function readVarint(b, p) {
  // Arithmetic (not bitwise) so tags above 2^31 stay correct.
  var v = 0, mul = 1;
  for (var i = 0; i < 10; i++) {
    if (p >= b.length) throw new Error("eof");
    var c = b[p++];
    v += (c & 0x7f) * mul;
    if ((c & 0x80) === 0) return [v, p];
    mul *= 128;
  }
  throw new Error("varint too long");
}

function varint(n) {
  var out = [];
  while (n >= 128) { out.push((n % 128) | 128); n = Math.floor(n / 128); }
  out.push(n);
  return out;
}

function concat(arrs) {
  var n = 0, i;
  for (i = 0; i < arrs.length; i++) n += arrs[i].length;
  var out = new Uint8Array(n), o = 0;
  for (i = 0; i < arrs.length; i++) { out.set(arrs[i], o); o += arrs[i].length; }
  return out;
}

function encodeLD(no, payload) {
  return concat([varint(no * 8 + 2), varint(payload.length), payload]);
}

function parse(b) {
  var out = [], p = 0;
  while (p < b.length) {
    var s = p, t = readVarint(b, p);
    p = t[1];
    var no = Math.floor(t[0] / 8), wt = t[0] % 8, ps = p, pe;
    if (no < 1) throw new Error("bad tag");
    if (wt === 0) { p = readVarint(b, p)[1]; pe = p; }
    else if (wt === 1) { p += 8; pe = p; }
    else if (wt === 5) { p += 4; pe = p; }
    else if (wt === 2) { var l = readVarint(b, p); p = l[1]; ps = p; p += l[0]; pe = p; }
    else throw new Error("unsupported wire type " + wt);
    if (p > b.length) throw new Error("overrun");
    out.push({ no: no, wt: wt, s: s, e: p, ps: ps, pe: pe });
  }
  return out;
}

// fn(payload) -> undefined (keep) | null (drop) | Uint8Array (replace payload)
function mapField(b, no, fn) {
  var f = parse(b), parts = [], last = 0, changed = false;
  for (var i = 0; i < f.length; i++) {
    var x = f[i];
    if (x.no !== no || x.wt !== 2) continue;
    var r = fn(b.subarray(x.ps, x.pe));
    if (r === undefined) continue;
    parts.push(b.subarray(last, x.s));
    last = x.e;
    changed = true;
    if (r !== null) parts.push(encodeLD(no, r));
  }
  if (!changed) return b;
  parts.push(b.subarray(last));
  return concat(parts);
}

// like mapField, but fn returns the same reference when nothing changed
function edit(b, no, fn) {
  return mapField(b, no, function (p) {
    var r = fn(p);
    return r === p ? undefined : r;
  });
}

function dropFields(b, nos) {
  var f = parse(b), parts = [], last = 0, changed = false;
  for (var i = 0; i < f.length; i++) {
    if (nos.indexOf(f[i].no) >= 0) {
      parts.push(b.subarray(last, f[i].s));
      last = f[i].e;
      changed = true;
    }
  }
  if (!changed) return b;
  parts.push(b.subarray(last));
  return concat(parts);
}

function has(b, no) {
  var f = parse(b);
  for (var i = 0; i < f.length; i++) if (f[i].no === no) return true;
  return false;
}

// read a varint scalar at a nested path; undefined if missing
function getVarint(b, path) {
  var f = parse(b);
  for (var i = 0; i < f.length; i++) {
    var x = f[i];
    if (x.no !== path[0]) continue;
    if (path.length === 1) return x.wt === 0 ? readVarint(b, x.ps)[0] : undefined;
    if (x.wt !== 2) continue;
    var r = getVarint(b.subarray(x.ps, x.pe), path.slice(1));
    if (r !== undefined) return r;
  }
  return undefined;
}

// read an ASCII string at a nested path; undefined if missing / non-ASCII
function getAscii(b, path) {
  var f = parse(b);
  for (var i = 0; i < f.length; i++) {
    var x = f[i];
    if (x.no !== path[0] || x.wt !== 2) continue;
    var inner = b.subarray(x.ps, x.pe);
    if (path.length === 1) {
      var s = "";
      for (var k = 0; k < inner.length; k++) {
        if (inner[k] > 127) return undefined;
        s += String.fromCharCode(inner[k]);
      }
      return s;
    }
    var r = getAscii(inner, path.slice(1));
    if (r !== undefined) return r;
  }
  return undefined;
}

// set varint at path = [msg, msg, ..., leaf]; creates missing messages
function setVarintAtPath(b, path, val) {
  var no = path[0], rest = path.slice(1), f = parse(b), idx = -1, i;
  for (i = 0; i < f.length; i++) if (f[i].no === no) { idx = i; break; }
  if (rest.length === 0) {
    var enc = concat([varint(no * 8), varint(val)]);
    if (idx >= 0) {
      if (f[idx].wt !== 0) return b;
      if (readVarint(b, f[idx].ps)[0] === val) return b;
      return concat([b.subarray(0, f[idx].s), enc, b.subarray(f[idx].e)]);
    }
    return concat([b, enc]);
  }
  if (idx >= 0) {
    if (f[idx].wt !== 2) return b;
    var inner = b.subarray(f[idx].ps, f[idx].pe);
    var r = setVarintAtPath(inner, rest, val);
    if (r === inner) return b;
    return concat([b.subarray(0, f[idx].s), encodeLD(no, r), b.subarray(f[idx].e)]);
  }
  return concat([b, encodeLD(no, setVarintAtPath(new Uint8Array(0), rest, val))]);
}

// apply fn to message field `no`; create it (empty) if absent
function upsertMsg(b, no, fn) {
  if (has(b, no)) return edit(b, no, fn);
  return concat([b, encodeLD(no, fn(new Uint8Array(0)))]);
}

function asciiBytes(s) {
  var o = new Uint8Array(s.length);
  for (var i = 0; i < s.length; i++) o[i] = s.charCodeAt(i) & 0x7f;
  return o;
}

function containsAscii(b, needle) {
  var n = asciiBytes(needle), nl = n.length;
  outer: for (var i = 0; i + nl <= b.length; i++) {
    if (b[i] !== n[0]) continue;
    for (var j = 1; j < nl; j++) if (b[i + j] !== n[j]) continue outer;
    return true;
  }
  return false;
}

/* ------------------------------------------------------------------ */
/* 2. features                                                         */
/* ------------------------------------------------------------------ */

// VERIFIED (schema): Player.adPlacements = 7, Player.adSlots = 68
var PLAYER_AD_FIELDS = [7, 68];

// UNVERIFIED heuristic markers for feed ad items (from third-party reports)
var FEED_AD_MARKERS = ["aboutthisad", "paralleladinteraction", "/pagead/"];

// UNVERIFIED browseIds of bottom-bar tabs (edit here if the app changes)
var TAB_SHORTS = "FEshorts";
var TAB_UPLOAD = "FEuploads";
var TAB_IMMERSIVE = "FEmusic_immersive";
var TAB_MUSIC_UPGRADE = "SPunlimited";

function isFeedAd(item) {
  for (var i = 0; i < FEED_AD_MARKERS.length; i++)
    if (containsAscii(item, FEED_AD_MARKERS[i])) return true;
  return false;
}

// ---- /player and the player part of /get_watch ----------------------
function processPlayer(b, o) {
  b = dropFields(b, PLAYER_AD_FIELDS);

  // EXPERIMENTAL: PiP + background play flags.
  // Schema: Player.playabilityStatus=2; .pictureInPictureRender=21 ->
  //   .pictureInPictureAbility=151635310 -> .active=1;
  //   .backgroundPlayerRender=11 -> .backgroundAbility=64657230 -> .active=1
  b = upsertMsg(b, 2, function (s) {
    s = setVarintAtPath(s, [21, 151635310, 1], 1);
    s = setVarintAtPath(s, [11, 64657230, 1], 1);
    return s;
  });

  // EXPERIMENTAL: caption translation via YouTube's own `tlang` parameter.
  // Schema: Player.captions=10 -> .playerCaptionsTrackListRenderer=51621377
  //   -> .captionTracks=1 -> .baseUrl=1
  if (o.captionLang !== "off") {
    var add = asciiBytes("&tlang=" + o.captionLang);
    b = edit(b, 10, function (c) {
      return edit(c, 51621377, function (l) {
        return edit(l, 1, function (t) {
          return edit(t, 1, function (url) {
            return containsAscii(url, "tlang=") ? url : concat([url, add]);
          });
        });
      });
    });
  }
  return b;
}

// ---- /get_watch ------------------------------------------------------
// VERIFIED (schema): Watch.contents=1 -> Content.player=2, Content.next=3
function processWatch(b, o) {
  return edit(b, 1, function (c) {
    c = edit(c, 2, function (p) { return processPlayer(p, o); });
    c = edit(c, 3, function (n) { return processNextBody(n); });
    return c;
  });
}

// ---- feed filtering (browse / next / search) -------------------------
// VERIFIED (schema paths):
//   Content.sectionListRenderer=49399797 -> .sectionListSupportedRenderers=1
//     -> .itemSectionRenderer=50195462 -> .richItemContents=1
//     -> .shelfRenderer=51845067 -> .richSectionContent=5
//        -> .reelShelfRenderer=51431404 -> .richItemContents=1
//   Content.singleColumnResultsRenderer=58173949 -> .tabs=1
//     -> .tabRenderer=58174010 -> .content=4 (Content)
function filterItems(sec) {
  return edit(sec, 1, function (item) { return isFeedAd(item) ? null : item; });
}
function sectionList(sl) {
  return edit(sl, 1, function (sup) {
    sup = edit(sup, 50195462, filterItems);
    sup = edit(sup, 51845067, function (shelf) {
      return edit(shelf, 5, function (rsc) { return edit(rsc, 51431404, filterItems); });
    });
    return sup;
  });
}
function content(c) {
  c = edit(c, 49399797, sectionList);
  c = edit(c, 58173949, function (sc) {
    return edit(sc, 1, function (tab) {
      return edit(tab, 58174010, function (tr) { return edit(tr, 4, content); });
    });
  });
  return c;
}

// VERIFIED (schema): Browse.content=9, Browse.onResponseReceivedAction=10
function processBrowse(b) {
  b = edit(b, 9, content);
  return edit(b, 10, content);
}
// VERIFIED (schema): Next.content=7 -> .nextResult=51779735 -> .content=1;
//                    Next.onResponseReceivedAction=8
function processNextBody(b) {
  b = edit(b, 7, function (n) {
    return edit(n, 51779735, function (nr) { return edit(nr, 1, content); });
  });
  return edit(b, 8, content);
}
// VERIFIED (schema): Search.content=4; Search.onResponseReceivedCommand=7
//   -> .itemSectionRenderer=50195462, .appendContinuationItemsAction=49399797
function processSearch(b) {
  b = edit(b, 4, content);
  return edit(b, 7, function (cmd) {
    cmd = edit(cmd, 50195462, filterItems);
    return edit(cmd, 49399797, sectionList);
  });
}

// ---- Shorts: drop entries flagged as ads -----------------------------
// VERIFIED (schema): Shorts.entries=2 -> Entry.command=1
//   -> Command.reelWatchEndpoint=139608561 -> .adClientParams=16 -> .isAd=1
function processShorts(b) {
  return edit(b, 2, function (e) {
    return getVarint(e, [1, 139608561, 16, 1]) === 1 ? null : e;
  });
}

// ---- Guide: hide bottom-bar tabs by browseId -------------------------
// VERIFIED (schema): Guide.labelItems=4 / iconItems=6 -> Item.guideSectionRenderer
//   =117866661 -> .rendererItems=1 -> RendererItem.iconRender=318370163 /
//   .labelRender=117501096 -> guideEntryRenderer.browseId=1
function processGuide(b, hide) {
  var itemFn = function (item) {
    return edit(item, 117866661, function (sec) {
      return edit(sec, 1, function (ri) {
        var id = getAscii(ri, [318370163, 1]) || getAscii(ri, [117501096, 1]);
        return id && hide[id] === true ? null : ri;
      });
    });
  };
  b = edit(b, 4, itemFn);
  return edit(b, 6, itemFn);
}

// ---- Settings: expose the background-play switch ---------------------
// VERIFIED (schema): Setting.settingItems=6 / CollectionItems=7 ->
//   SettingItem.backgroundPlayBackSettingRenderer=88478200 -> .backgroundPlayback=2
function processSettings(b) {
  var fn = function (item) {
    return has(item, 88478200)
      ? edit(item, 88478200, function (r) { return setVarintAtPath(r, [2], 1); })
      : item;
  };
  b = edit(b, 6, fn);
  return edit(b, 7, fn);
}

/* ------------------------------------------------------------------ */
/* 3. arguments                                                        */
/* ------------------------------------------------------------------ */

function truthy(v) { return v === true || v === 1 || v === "true" || v === "1"; }

function parseArgs(raw) {
  var order = ["blockUpload", "blockShorts", "blockImmersive", "captionLang", "debug"];
  var o = {};
  try {
    if (Array.isArray(raw)) {
      for (var i = 0; i < order.length; i++) if (raw[i] !== undefined) o[order[i]] = raw[i];
    } else if (raw && typeof raw === "object") {
      o = raw;
    } else if (typeof raw === "string") {
      var s = raw.trim();
      if (s.charAt(0) === "{" && s.indexOf(":") > 0) {
        o = JSON.parse(s);
      } else {
        s = s.replace(/^[\[{]\s*/, "").replace(/\s*[\]}]$/, "");
        var parts = s.split(",");
        for (var j = 0; j < order.length && j < parts.length; j++) {
          o[order[j]] = parts[j].trim().replace(/^["']|["']$/g, "");
        }
      }
    }
  } catch (e) { o = {}; }
  var lang = String(o.captionLang === undefined ? "off" : o.captionLang).trim();
  // whitelist: this value is appended to a URL, so only language-code shapes pass
  if (!/^[A-Za-z]{2,3}(-[A-Za-z0-9]{2,8})?$/.test(lang)) lang = "off";
  return {
    blockUpload: truthy(o.blockUpload),
    blockShorts: truthy(o.blockShorts),
    blockImmersive: truthy(o.blockImmersive),
    captionLang: lang,
    debug: truthy(o.debug)
  };
}

/* ------------------------------------------------------------------ */
/* 4. dispatcher                                                       */
/* ------------------------------------------------------------------ */

function transform(endpoint, body, o) {
  switch (endpoint) {
    case "player": return processPlayer(body, o);
    case "get_watch": return processWatch(body, o);
    case "browse": return processBrowse(body);
    case "next": return processNextBody(body);
    case "search": return processSearch(body);
    case "reel/reel_watch_sequence": return processShorts(body);
    case "account/get_setting": return processSettings(body);
    case "guide":
      var hide = {};
      hide[TAB_MUSIC_UPGRADE] = true;
      if (o.blockShorts) hide[TAB_SHORTS] = true;
      if (o.blockUpload) hide[TAB_UPLOAD] = true;
      if (o.blockImmersive) hide[TAB_IMMERSIVE] = true;
      return processGuide(body, hide);
    default: return body;
  }
}

function main() {
  var o = parseArgs(typeof $argument === "undefined" ? undefined : $argument);
  try {
    var m = /^https:\/\/youtubei\.googleapis\.com\/youtubei\/v1\/([\w\/]+)/i.exec($request.url);
    var body = $response.bodyBytes || $response.body;
    if (!m || !body || typeof body === "string") return $done({});
    if (body instanceof ArrayBuffer) body = new Uint8Array(body);
    var ep = m[1].toLowerCase();
    var out = transform(ep, body, o);
    if (out === body) {
      if (o.debug) console.log("[YouTubeClean] " + ep + ": no change");
      return $done({});
    }
    if (o.debug) console.log("[YouTubeClean] " + ep + ": " + body.length + " -> " + out.length + " bytes");
    return $done({ body: out });
  } catch (e) {
    if (o.debug) console.log("[YouTubeClean] error, passing through: " + e);
    return $done({}); // fail-open
  }
}

if (typeof $done === "function" && typeof $response !== "undefined") {
  main();
}
if (typeof module !== "undefined" && module.exports) {
  module.exports = {
    parse: parse, mapField: mapField, edit: edit, dropFields: dropFields,
    setVarintAtPath: setVarintAtPath, getVarint: getVarint, getAscii: getAscii,
    transform: transform, parseArgs: parseArgs, varint: varint, readVarint: readVarint,
    encodeLD: encodeLD, concat: concat, containsAscii: containsAscii
  };
}
