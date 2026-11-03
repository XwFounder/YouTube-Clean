/*
 * YouTube_Clean_response.js — v1.3
 *
 * Loon http-response 脚本，作用于 https://youtubei.googleapis.com/youtubei/v1/*
 * （YouTube / YouTube Music iOS App，protobuf 响应体，binary-body-mode）
 *
 * 功能
 *   1. 去广告：player 的 adPlacements / adSlots / playbackTracking.pageadViewthroughconversion；
 *      browse / next / search 信息流里的广告条目（递归、与嵌套层级无关）；Shorts 里 isAd 的分片。
 *   2. 画中画 + 后台播放：player.playabilityStatus 打开 pictureInPictureAbility / backgroundAbility。
 *   3. 字幕翻译：在字幕轨里追加一条目标语言的译文轨（baseUrl + &tlang=），并设为默认音轨的默认字幕。
 *      v1.1：基准轨按「可翻译 +4 / asr +2 / en +2」打分挑选（原来是"第一条 en 或第 0 条"，
 *            遇到人工上传的不可翻译轨会造出加载失败的译文轨），译文轨继承基准轨的 kind。
 *   4. 歌词翻译：把 timedLyricsRender / 歌词 shelf 的文本按行翻译后写回。
 *   5. 底栏净化：guide 里按 browseId 隐藏 Shorts / 上传 / 选段 / 升级 入口。
 *   6. 后台播放开关：account/get_setting 里 backgroundPlayback 置 1。
 *
 * 安全约束（可 grep 自证）
 *   - 唯一的网络访问是注释中标了 [NET] 的歌词翻译请求（captionLang=off 时完全不联网）
 *   - 不读写 $persistentStore / localStorage，不读取、不输出请求头与 Cookie
 *   - 无 eval / Function / 动态代码
 *   - 失败即放行（fail-open）：任何异常都返回原响应，绝不阻塞 App
 *   - 改动是字节级 splice：未显式修改的字段逐字节保持不变
 *
 * 字段号来源：Maasea/sgmodule 内嵌的 protobuf schema（Apache-2.0, build 2026/7/19）
 * 参数顺序（与 kelee 参考插件一致，兼容对象/数组两种 $argument）：
 *   blockUpload, blockShorts, blockImmersive, captionLang, debug
 *   歌词翻译语言默认跟随 captionLang（可选 lyricLang 单独覆盖）
 */

"use strict";

/* ================================================================== */
/* 0. 常量                                                             */
/* ================================================================== */

var DEFAULT_CAPTION_LANG = "zh-Hans";  // 与参考插件 [Argument] captionLang 的默认值一致
var MAX_DEPTH = 40;              // 递归深度上限（真实响应约 10~20 层）
var WALK_BUDGET_FACTOR = 12;     // 单次深度遍历允许解析的字节数 = body.length * 12
var LYRIC_TIMEOUT_MS = 4000;     // 单次翻译请求超时
var LYRIC_TOTAL_MS = 9000;       // 歌词翻译总预算，超时直接放行
var LYRIC_CHUNK_CHARS = 1400;    // 单个翻译请求的文本上限

var TR_URL = "https://translate.googleapis.com/translate_a/single"; // [NET]

// Player 层的广告字段（schema 已核实）
var PLAYER_AD_FIELDS = [7, 68];
var PLAYER_TRACKING = 9;
var PLAYER_TRACKING_PAGEAD = 18;

// 广告条目在字节里留下的特征值（都是只有广告体才会出现的字符串）
var AD_MARKERS = ["pagead", "aboutthisad", "paralleladinteraction"];

// 底栏 / 侧栏入口的 browseId（命中即隐藏）
var GUIDE_IDS = {
  shorts: ["FEshorts", "FEmusic_shorts"],
  upload: ["FEuploads", "FEmusic_uploads"],
  immersive: ["FEmusic_immersive", "FEmusic_clips"],
  upgrade: ["SPunlimited", "FEmusic_premium", "FEmusic_upgrade"]
};

// 字幕翻译可选的译文语言（写进 translationLanguages，App 的"自动翻译"菜单用它）
var LANG_NAMES = [
  ["zh-Hans", "简体中文"],
  ["zh-Hant", "繁體中文"],
  ["en", "English"],
  ["ja", "日本語"],
  ["ko", "한국어"],
  ["fr", "Français"],
  ["de", "Deutsch"],
  ["ru", "Русский"],
  ["vi", "Tiếng Việt"],
  ["fil", "Filipino"]
];

/* ================================================================== */
/* 1. UTF-8（JSC 里没有 TextDecoder/TextEncoder，自己来）               */
/* ================================================================== */

function utf8Encode(str) {
  var out = [], i, c, c2, cp;
  for (i = 0; i < str.length; i++) {
    c = str.charCodeAt(i);
    if (c < 0x80) {
      out.push(c);
    } else if (c < 0x800) {
      out.push(0xc0 | (c >> 6), 0x80 | (c & 0x3f));
    } else if (c >= 0xd800 && c <= 0xdbff && i + 1 < str.length &&
               str.charCodeAt(i + 1) >= 0xdc00 && str.charCodeAt(i + 1) <= 0xdfff) {
      c2 = str.charCodeAt(i + 1);
      cp = 0x10000 + ((c - 0xd800) << 10) + (c2 - 0xdc00);
      out.push(0xf0 | (cp >> 18), 0x80 | ((cp >> 12) & 0x3f),
               0x80 | ((cp >> 6) & 0x3f), 0x80 | (cp & 0x3f));
      i++;
    } else if (c >= 0xd800 && c <= 0xdfff) {
      out.push(0xef, 0xbf, 0xbd); // 落单的代理对 -> U+FFFD
    } else {
      out.push(0xe0 | (c >> 12), 0x80 | ((c >> 6) & 0x3f), 0x80 | (c & 0x3f));
    }
  }
  return new Uint8Array(out);
}

function utf8Decode(b) {
  var s = "", i = 0, c, c1, c2, c3, cp;
  while (i < b.length) {
    c = b[i++];
    if (c < 0x80) {
      s += String.fromCharCode(c);
    } else if (c >= 0xc0 && c < 0xe0) {
      if (i >= b.length) break;
      c1 = b[i++] & 0x3f;
      s += String.fromCharCode(((c & 0x1f) << 6) | c1);
    } else if (c >= 0xe0 && c < 0xf0) {
      if (i + 1 >= b.length) break;
      c1 = b[i++] & 0x3f;
      c2 = b[i++] & 0x3f;
      s += String.fromCharCode(((c & 0x0f) << 12) | (c1 << 6) | c2);
    } else if (c >= 0xf0) {
      if (i + 2 >= b.length) break;
      c1 = b[i++] & 0x3f;
      c2 = b[i++] & 0x3f;
      c3 = b[i++] & 0x3f;
      cp = (((c & 0x07) << 18) | (c1 << 12) | (c2 << 6) | c3) - 0x10000;
      s += String.fromCharCode(0xd800 + (cp >> 10), 0xdc00 + (cp & 0x3ff));
    } else {
      s += "\ufffd";
    }
  }
  return s;
}

/* ================================================================== */
/* 2. protobuf 线格式（无 schema，只做定位与替换）                       */
/* ================================================================== */

function readVarint(b, p) {
  // 用算术而不是位运算，tag 大于 2^31 时也正确
  var v = 0, mul = 1, c;
  for (var i = 0; i < 10; i++) {
    if (p >= b.length) throw new Error("eof");
    c = b[p++];
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
  var n = 0, i, o = 0;
  for (i = 0; i < arrs.length; i++) n += arrs[i].length;
  var out = new Uint8Array(n);
  for (i = 0; i < arrs.length; i++) { out.set(arrs[i], o); o += arrs[i].length; }
  return out;
}

function encodeLD(no, payload) {
  return concat([new Uint8Array(varint(no * 8 + 2)), new Uint8Array(varint(payload.length)), payload]);
}

function encodeVarintField(no, val) {
  return concat([new Uint8Array(varint(no * 8)), new Uint8Array(varint(val))]);
}

function parse(b) {
  var out = [], p = 0, s, t, no, wt, ps, pe;
  while (p < b.length) {
    s = p;
    t = readVarint(b, p);
    p = t[1];
    no = Math.floor(t[0] / 8);
    wt = t[0] % 8;
    ps = p;
    if (no < 1) throw new Error("bad tag");
    if (wt === 0) { p = readVarint(b, p)[1]; pe = p; }
    else if (wt === 1) { p += 8; pe = p; }
    else if (wt === 5) { p += 4; pe = p; }
    else if (wt === 2) { var l = readVarint(b, p); p = l[1]; ps = p; p += l[0]; pe = p; }
    else throw new Error("unsupported wire type " + wt);
    if (p > b.length || p < ps) throw new Error("overrun");
    out.push({ no: no, wt: wt, s: s, e: p, ps: ps, pe: pe });
  }
  return out;
}

function looksLikeMessage(b) {
  if (!b || b.length < 2) return false;
  try { parse(b); return true; } catch (e) { return false; }
}

// 同名（同字段号）重复字段的载荷列表
function getRepeated(b, no) {
  var f = parse(b), out = [], i;
  for (i = 0; i < f.length; i++) if (f[i].no === no && f[i].wt === 2) out.push(b.subarray(f[i].ps, f[i].pe));
  return out;
}

// 取第一个该字段号出现的位置（不限 wire type）
function firstField(b, no) {
  var f = parse(b), i;
  for (i = 0; i < f.length; i++) if (f[i].no === no) return f[i];
  return null;
}

function getStr(b, no) {
  var x = firstField(b, no);
  if (!x || x.wt !== 2) return undefined;
  return utf8Decode(b.subarray(x.ps, x.pe));
}

function getStrPath(b, path) {
  var cur = b, i, x, next;
  for (i = 0; i < path.length; i++) {
    x = firstField(cur, path[i]);
    if (!x || x.wt !== 2) return undefined;
    next = cur.subarray(x.ps, x.pe);
    if (i === path.length - 1) return utf8Decode(next);
    cur = next;
  }
  return undefined;
}

function getVarint(b, no) {
  var x = firstField(b, no);
  if (!x || x.wt !== 0) return undefined;
  return readVarint(b, x.ps)[0];
}

function getVarintPath(b, path) {
  var cur = b, i, x;
  for (i = 0; i < path.length - 1; i++) {
    x = firstField(cur, path[i]);
    if (!x || x.wt !== 2) return undefined;
    cur = cur.subarray(x.ps, x.pe);
  }
  return getVarint(cur, path[path.length - 1]);
}

function hasField(b, no) {
  var f = parse(b), i;
  for (i = 0; i < f.length; i++) if (f[i].no === no) return true;
  return false;
}

// 对字段 no 的每一处 wt=2 载荷调用 fn：undefined/同引用=保留，null=删除，Uint8Array=替换
function edit(b, no, fn) {
  var f = parse(b), parts = [], last = 0, changed = false, i, x, payload, r;
  for (i = 0; i < f.length; i++) {
    x = f[i];
    if (x.no !== no || x.wt !== 2) continue;
    payload = b.subarray(x.ps, x.pe);
    r = fn(payload);
    if (r === undefined || r === payload) continue;
    parts.push(b.subarray(last, x.s));
    last = x.e;
    changed = true;
    if (r !== null) parts.push(encodeLD(no, r));
  }
  if (!changed) return b;
  parts.push(b.subarray(last));
  return concat(parts);
}

function dropFields(b, nos) {
  var f = parse(b), parts = [], last = 0, changed = false, i;
  for (i = 0; i < f.length; i++) {
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

// 把字段 no 的所有出现替换为 payloads（按原第一次出现的位置展开）
function replaceRepeated(b, no, payloads) {
  var f = parse(b), parts = [], last = 0, i, x, placed = false, k;
  for (i = 0; i < f.length; i++) {
    x = f[i];
    if (x.no !== no) continue;
    parts.push(b.subarray(last, x.s));
    last = x.e;
    if (!placed) {
      placed = true;
      for (k = 0; k < payloads.length; k++) parts.push(encodeLD(no, payloads[k]));
    }
  }
  if (!placed) {
    parts = [b];
    for (k = 0; k < payloads.length; k++) parts.push(encodeLD(no, payloads[k]));
    return concat(parts);
  }
  parts.push(b.subarray(last));
  return concat(parts);
}

// 标量 varint 写入（重复出现只保留一个）
function setVarint(b, no, val) {
  var f = parse(b), occ = [], i, x, parts, last, placed;
  for (i = 0; i < f.length; i++) if (f[i].no === no && f[i].wt === 0) occ.push(f[i]);
  if (occ.length === 1 && readVarint(b, occ[0].ps)[0] === val) return b;
  parts = [];
  last = 0;
  placed = false;
  for (i = 0; i < f.length; i++) {
    x = f[i];
    if (x.no !== no || x.wt !== 0) continue;
    parts.push(b.subarray(last, x.s));
    last = x.e;
    if (!placed) { parts.push(encodeVarintField(no, val)); placed = true; }
  }
  if (!placed) return concat([b, encodeVarintField(no, val)]);
  parts.push(b.subarray(last));
  return concat(parts);
}

// 字符串字段写入（覆盖第一次出现，删除多余出现）
function setStr(b, no, str) {
  return setBytes(b, no, utf8Encode(str));
}

function setBytes(b, no, bytes) {
  return replaceRepeated(b, no, [bytes]);
}

// 字段 no 存在则就地改，不存在则追加
function upsertMsg(b, no, fn) {
  if (hasField(b, no)) return edit(b, no, fn);
  return concat([b, encodeLD(no, fn(new Uint8Array(0)))]);
}

function appendLD(b, no, payload) {
  return concat([b, encodeLD(no, payload)]);
}

function asciiBytes(s) {
  var o = new Uint8Array(s.length), i;
  for (i = 0; i < s.length; i++) o[i] = s.charCodeAt(i) & 0x7f;
  return o;
}

function containsAscii(b, needle) {
  var n = asciiBytes(needle), nl = n.length, i, j, hit;
  if (nl === 0 || nl > b.length) return false;
  outer:
  for (i = 0; i + nl <= b.length; i++) {
    if (b[i] !== n[0]) continue;
    hit = true;
    for (j = 1; j < nl; j++) {
      if (b[i + j] !== n[j]) { hit = false; break; }
    }
    if (hit) return true;
  }
  return false;
}

/* ---- 深度遍历（与嵌套层级无关，带解析预算） ---- */

function newCtx(b) {
  return { budget: Math.max(1 << 18, b.length * WALK_BUDGET_FACTOR * 3) };
}

function deepEdit(b, no, fn) {
  return deepEditInner(b, function (n) { return n === no ? fn : null; }, 0, newCtx(b));
}

// 一次遍历处理多个字段号：map 形如 {50195462: fn, 51431404: fn}
function deepEditMulti(b, map) {
  return deepEditInner(b, function (n) { return map[n] || null; }, 0, newCtx(b));
}

function deepEditInner(b, pick, depth, ctx) {
  if (depth > MAX_DEPTH) return b;
  ctx.budget -= b.length;
  if (ctx.budget < 0) return b;
  var f = parse(b), parts = [], last = 0, changed = false, i, x, payload, r, np, fn;
  for (i = 0; i < f.length; i++) {
    x = f[i];
    if (x.wt !== 2) continue;
    payload = b.subarray(x.ps, x.pe);
    fn = pick(x.no);
    if (fn) {
      r = fn(payload, x.no);
      if (r === undefined || r === payload) continue;
      parts.push(b.subarray(last, x.s));
      last = x.e;
      changed = true;
      if (r !== null) parts.push(encodeLD(x.no, r));
      continue;
    }
    if (!looksLikeMessage(payload)) continue;
    np = deepEditInner(payload, pick, depth + 1, ctx);
    if (np === payload) continue;
    parts.push(b.subarray(last, x.s));
    parts.push(encodeLD(x.no, np));
    last = x.e;
    changed = true;
  }
  if (!changed) return b;
  parts.push(b.subarray(last));
  return concat(parts);
}

/* ================================================================== */
/* 3. 广告                                                             */
/* ================================================================== */

function isAdBlob(b) {
  var i;
  for (i = 0; i < AD_MARKERS.length; i++) if (containsAscii(b, AD_MARKERS[i])) return true;
  return false;
}

// 条目容器（schema 已核实）：
//   ItemSectionRenderer=50195462.richItemContents=1
//   ReelShelfRenderer=51431404.richItemContents=1
// 只在这些容器的"条目槽位"上判广告，绝不按整棵子树判断 ——
// 否则广告的祖先节点也含特征值，会把整块信息流一起删掉。
function dropAdItems(sec) {
  return edit(sec, 1, function (item) {
    return isAdBlob(item) ? null : undefined;
  });
}

function removeAds(b) {
  var map = {};
  map[50195462] = dropAdItems;
  map[51431404] = dropAdItems;
  return deepEditMulti(b, map);
}

// Shorts：入口的 command.reelWatchEndpoint.adClientParams.isAd == 1
function isAdShortsEntry(p) {
  var cmd, ep, params;
  if (!looksLikeMessage(p)) return false;
  var c = firstField(p, 1);
  if (!c || c.wt !== 2) return false;
  cmd = p.subarray(c.ps, c.pe);
  var e = firstField(cmd, 139608561);
  if (!e || e.wt !== 2) return false;
  ep = cmd.subarray(e.ps, e.pe);
  var a = firstField(ep, 16);
  if (!a || a.wt !== 2) return false;
  params = ep.subarray(a.ps, a.pe);
  return getVarint(params, 1) === 1;
}

function stripShortsAds(b, depth, ctx) {
  if (depth > MAX_DEPTH) return b;
  ctx.budget -= b.length;
  if (ctx.budget < 0) return b;
  var f = parse(b), parts = [], last = 0, changed = false, i, x, payload, np;
  for (i = 0; i < f.length; i++) {
    x = f[i];
    if (x.wt !== 2) continue;
    payload = b.subarray(x.ps, x.pe);
    if (isAdShortsEntry(payload)) {
      parts.push(b.subarray(last, x.s));
      last = x.e;
      changed = true;
      continue;
    }
    if (!looksLikeMessage(payload)) continue;
    np = stripShortsAds(payload, depth + 1, ctx);
    if (np === payload) continue;
    parts.push(b.subarray(last, x.s));
    parts.push(encodeLD(x.no, np));
    last = x.e;
    changed = true;
  }
  if (!changed) return b;
  parts.push(b.subarray(last));
  return concat(parts);
}

/* ================================================================== */
/* 4. player：广告 + 画中画 + 后台播放 + 字幕翻译                        */
/* ================================================================== */

function enablePlayability(ps) {
  // PlayabilityStatus.pictureInPictureRender=21 -> PictureInPictureSupportedRenderer
  //   .pictureInPictureAbility=151635310 -> {active=1, f4=4, f6=6, f8=8}
  ps = upsertMsg(ps, 21, function (pip) {
    return upsertMsg(pip, 151635310, function (ab) {
      ab = setVarint(ab, 1, 1);
      ab = setVarint(ab, 4, 0);
      ab = setVarint(ab, 6, 0);
      ab = setVarint(ab, 8, 1);
      return ab;
    });
  });
  // PlayabilityStatus.backgroundPlayerRender=11 -> BackgroundSupportedRenderer
  //   .backgroundAbility=64657230 -> {active=1}
  return upsertMsg(ps, 11, function (bg) {
    return upsertMsg(bg, 64657230, function (ab) {
      return setVarint(ab, 1, 1);
    });
  });
}

function labelOf(text) {
  // Label{runs:[Run{text}]}
  return encodeLD(1, encodeLD(1, utf8Encode(text)));
}

function buildTranslatedTrack(baseUrl, lang, kind) {
  // CaptionTrack{baseUrl=1, name=2(Label), vssId=3, languageCode=4, kind=5, isTranslatable=7}
  var parts = [
    encodeLD(1, utf8Encode(baseUrl)),
    encodeLD(2, labelOf("译文 " + lang)),
    encodeLD(3, utf8Encode("." + lang)),
    encodeLD(4, utf8Encode(lang))
  ];
  if (kind) parts.push(encodeLD(5, utf8Encode(kind)));   // 跟随基准轨：asr 轨派生的译文轨也得是 asr
  parts.push(encodeVarintField(7, 1));
  return concat(parts);
}

/* 选翻译基准轨：服务端只对「可翻译」的轨接受 tlang。
   打分：可翻译 +4、asr +2、en +2；目标语言轨不参与（它就是结果，不值得再翻译一次）。 */
function trackScore(track, wantLang) {
  var lang = getStr(track, 4) || "";
  var kind = getStr(track, 5) || "";
  var s = 0;
  if (getVarint(track, 7) === 1) s += 4;
  if (kind === "asr") s += 2;
  if (lang === "en") s += 2;
  if (lang === wantLang) s -= 8;
  return s;
}

function packedInts(b, no) {
  // captionTrackIndices 可能是 packed(wt2) 也可能是 unpacked(wt0)
  var f = parse(b), out = [], i, j, x, p, t;
  for (i = 0; i < f.length; i++) {
    x = f[i];
    if (x.no !== no) continue;
    if (x.wt === 0) { out.push(readVarint(b, x.ps)[0]); continue; }
    if (x.wt !== 2) continue;
    p = x.ps;
    while (p < x.pe) { t = readVarint(b, p); out.push(t[0]); p = t[1]; }
  }
  return out;
}

function translationLanguages(target) {
  var list = [], i, langs = [], hit = false, name;
  for (i = 0; i < LANG_NAMES.length; i++) langs.push(LANG_NAMES[i]);
  for (i = 0; i < langs.length; i++) if (langs[i][0] === target) { hit = true; break; }
  if (!hit) langs.unshift([target, target]);
  for (i = 0; i < langs.length; i++) {
    name = langs[i][1];
    list.push(concat([encodeLD(1, utf8Encode(langs[i][0])), encodeLD(2, labelOf(name))]));
  }
  return list;
}

function translateCaptions(captions, lang) {
  var list = firstField(captions, 51621377);
  if (!list || list.wt !== 2) return captions;
  var body = captions.subarray(list.ps, list.pe);
  var tracks = getRepeated(body, 1);
  if (tracks.length === 0) return captions;

  var i, idx = -1, src = -1, srcKind = "", base, score, best = -999;
  for (i = 0; i < tracks.length; i++) {
    if (getStr(tracks[i], 4) === lang) { idx = i; break; }
  }
  if (idx < 0) {
    var anyTrans = false, anyFalse = false, anyAsr = false, flag;
    for (i = 0; i < tracks.length; i++) {
      flag = getVarint(tracks[i], 7);
      if (flag === 1) anyTrans = true; else if (flag === 0) anyFalse = true;
      if (getStr(tracks[i], 5) === "asr") anyAsr = true;
    }
    // 服务端只对「可翻译」的轨接受 tlang：全部轨都明确标注不可翻译时不造轨道，否则 App 会报字幕加载失败
    if (!anyTrans && !anyAsr && anyFalse) return captions;
    for (i = 0; i < tracks.length; i++) {
      score = trackScore(tracks[i], lang);
      if (score > best) { best = score; src = i; }
    }
    if (src < 0) return captions;
    base = getStr(tracks[src], 1);
    if (!base) return captions;                       // 没有 baseUrl 就不动
    srcKind = getStr(tracks[src], 5) || "";
    if (base.indexOf("tlang=") < 0) base = base + (base.indexOf("?") < 0 ? "?" : "&") + "tlang=" + lang;
    tracks.push(buildTranslatedTrack(base, lang, srcKind));
    idx = tracks.length - 1;
  }

  // 所有轨道都允许被翻译
  var n = [], k;
  for (i = 0; i < tracks.length; i++) n.push(setVarint(tracks[i], 7, 1));
  body = replaceRepeated(body, 1, n);

  // 音轨：把译文轨挂上去并设为默认字幕
  var audio = getRepeated(body, 2), na = [];
  for (i = 0; i < audio.length; i++) {
    var a = audio[i];
    var inds = packedInts(a, 2);
    if (inds.indexOf(idx) < 0) {
      inds.push(idx);
      // 合并成单个 packed 字段，避免出现两个 field 2
      var pk = [], q;
      for (q = 0; q < inds.length; q++) pk.push(new Uint8Array(varint(inds[q])));
      a = replaceRepeated(a, 2, [concat(pk)]);
    }
    a = setVarint(a, 3, idx);        // defaultCaptionTrackIndex
    a = setVarint(a, 11, 3);         // captionsInitialState = 字幕已开启
    na.push(a);
  }
  if (na.length > 0) body = replaceRepeated(body, 2, na);

  // 自动翻译菜单
  body = replaceRepeated(body, 3, translationLanguages(lang));

  // 轨道列表级别的默认字幕轨（没有 audioTracks 的响应也能默认开启字幕）
  body = setVarint(body, 6, idx);

  return replaceRepeated(captions, 51621377, [body]);
}

function processPlayer(b, o) {
  var adsBefore = hasField(b, 7) || hasField(b, 68) ||
    (function () {
      try { return getVarintPath(b, [PLAYER_TRACKING, PLAYER_TRACKING_PAGEAD]) !== null; } catch (e) { return false; }
    })();
  b = dropFields(b, PLAYER_AD_FIELDS);
  b = edit(b, PLAYER_TRACKING, function (t) { return dropFields(t, [PLAYER_TRACKING_PAGEAD]); });
  b = upsertMsg(b, 2, enablePlayability);              // Player.playabilityStatus=2
  if (o.captionLang !== "off") {
    b = edit(b, 10, function (c) { return translateCaptions(c, o.captionLang); });
  }
  logAlways(o, adsBefore ? "player_fields_removed" : "player_fields_not_found");
  return b;
}

/* v1.2：debug 打开时输出结构化诊断标记，供定位"脚本是否跑到、广告字段是否在场"
   response_script_entered / body_type_unsupported / protobuf_parse_failed /
   player_fields_removed / player_fields_not_found / response_script_completed
   不输出 Cookie、Authorization、令牌或完整请求头。 */

/* ================================================================== */
/* 5. guide（底栏/侧栏入口）                                            */
/* ================================================================== */

function hiddenGuideIds(o) {
  var ids = [];
  ids = ids.concat(GUIDE_IDS.upgrade);
  if (o.blockShorts) ids = ids.concat(GUIDE_IDS.shorts);
  if (o.blockUpload) ids = ids.concat(GUIDE_IDS.upload);
  if (o.blockImmersive) ids = ids.concat(GUIDE_IDS.immersive);
  return ids;
}

function guideItemId(item) {
  var id = getStrPath(item, [318370163, 1]);
  if (id) return id;
  return getStrPath(item, [117501096, 1]);
}

function isHiddenGuideItem(item, ids) {
  var id = guideItemId(item), k;
  if (id !== undefined) {
    for (k = 0; k < ids.length; k++) if (id === ids[k]) return true;
    return false;
  }
  // 兜底：browseId 藏在别的层级时，按特征字符串判断
  for (k = 0; k < ids.length; k++) if (containsAscii(item, ids[k])) return true;
  return false;
}

function processGuide(b, o) {
  var ids = hiddenGuideIds(o);
  b = deepEdit(b, 117866661, function (sec) {
    // GuideSectionRenderer.rendererItems=1
    var out = edit(sec, 1, function (item) {
      return isHiddenGuideItem(item, ids) ? null : undefined;
    });
    if (out !== sec && getRepeated(out, 1).length === 0) return null;  // 整段空了就删掉
    return out;
  });
  // 删掉因此变空的 guide 项（Guide.labelItems=4 / iconItems=6）
  var dropEmpty = function (item) { return item.length === 0 ? null : undefined; };
  b = edit(b, 4, dropEmpty);
  return edit(b, 6, dropEmpty);
}

/* ================================================================== */
/* 6. account/get_setting：后台播放开关                                 */
/* ================================================================== */

function processSettings(b) {
  return deepEdit(b, 88478200, function (r) {
    // BackgroundPlayBackSettingRenderer.backgroundPlayback=2
    return setVarint(r, 2, 1);
  });
}

/* ================================================================== */
/* 7. 歌词翻译                                                         */
/* ================================================================== */

function labelText(lab) {
  var runs = getRepeated(lab, 1), out = [], i, t;
  for (i = 0; i < runs.length; i++) {
    t = getStr(runs[i], 1);
    if (t !== undefined) out.push(t);
  }
  return out.join("");
}

// 遍历所有"歌词 run"：fnText(runText) -> 新文本 | undefined(不改)
function mapLyricRuns(b, fnText) {
  var rep = function (msg) {
    return edit(msg, 1, function (run) {
      var t = getStr(run, 1), nt;
      if (t === undefined) return undefined;
      nt = fnText(t);
      if (nt === undefined || nt === t) return undefined;
      return setStr(run, 1, nt);
    });
  };
  // browse: VideoContent.timedLyricsRender=465160965 -> timedLyricsContent=4 -> runs=1
  b = deepEdit(b, 465160965, function (tlr) {
    return edit(tlr, 4, rep);
  });
  // MusicDescriptionShelfRenderer=221496734 -> description=3(Label) -> runs=1
  b = deepEdit(b, 221496734, function (mds) {
    if (!isLyricsShelf(mds)) return undefined;
    return edit(mds, 3, rep);
  });
  return b;
}

// 只有"歌词"型 shelf 才翻：footer 里带 lyric/歌，或者描述本身就分成多行 run
function isLyricsShelf(mds) {
  var footer = firstField(mds, 10), ft = "", desc;
  if (footer && footer.wt === 2) ft = labelText(mds.subarray(footer.ps, footer.pe));
  if (/lyric|歌词|歌詞|letra|paroles|testo|tekst|lied|söz|가사/i.test(ft)) return true;
  desc = getRepeated(mds, 3)[0];
  return !!desc && getRepeated(desc, 1).length >= 3;
}

function lyricLines(b) {
  var lines = [], seen = {}, push = function (t) {
    var parts = String(t).split("\n"), i;
    for (i = 0; i < parts.length; i++) {
      var ln = parts[i];
      if (ln === "" || seen["|" + ln]) continue;
      seen["|" + ln] = true;
      lines.push(ln);
    }
  };
  mapLyricRuns(b, function (t) { push(t); return undefined; });
  return lines;
}

function applyLineMap(b, map) {
  return mapLyricRuns(b, function (t) {
    var parts = t.split("\n"), changed = false, i, m, out = [];
    for (i = 0; i < parts.length; i++) {
      m = map[parts[i]];
      if (m !== undefined && m !== "") { out.push(m); changed = true; }
      else out.push(parts[i]);
    }
    return changed ? out.join("\n") : undefined;
  });
}

/* [NET] 唯一的网络访问：谷歌翻译的免密接口 */
function httpGet(url) {
  return new Promise(function (resolve) {
    var done = false, finish = function (v) { if (!done) { done = true; resolve(v); } };
    var timer = setTimeout(function () { finish(null); }, LYRIC_TIMEOUT_MS);
    var ok = function (body) { clearTimeout(timer); finish(typeof body === "string" ? body : null); };
    var fail = function () { clearTimeout(timer); finish(null); };
    try {
      if (typeof $task !== "undefined" && $task && $task.fetch) {
        $task.fetch({ url: url }).then(function (r) { ok(r && r.body); }, fail);
      } else if (typeof $httpClient !== "undefined" && $httpClient && $httpClient.get) {
        $httpClient.get({ url: url }, function (err, resp, body) { if (err) fail(); else ok(body); });
      } else {
        fail();
      }
    } catch (e) {
      fail();
    }
  });
}

function parseTranslated(body) {
  try {
    var d = JSON.parse(body);
    if (!d || !d[0]) return null;
    var segs = d[0], out = [], i;
    for (i = 0; i < segs.length; i++) if (segs[i] && typeof segs[i][0] === "string") out.push(segs[i][0]);
    return out.join("");
  } catch (e) {
    return null;
  }
}

function translateText(text, lang) {
  var q;
  try { q = encodeURIComponent(text); } catch (e) { return Promise.resolve(null); }
  var url = TR_URL + "?client=gtx&dt=t&sl=auto&tl=" + encodeURIComponent(lang) + "&q=" + q;
  return httpGet(url).then(function (body) {
    if (!body) return null;
    return parseTranslated(body);
  }, function () { return null; });
}

function chunkLines(lines, max) {
  var chunks = [], cur = [], len = 0, i, l;
  for (i = 0; i < lines.length; i++) {
    l = lines[i];
    if (cur.length > 0 && len + l.length + 1 > max) { chunks.push(cur); cur = []; len = 0; }
    cur.push(l);
    len += l.length + 1;
  }
  if (cur.length) chunks.push(cur);
  return chunks;
}

// 逐块翻译；只有"行数对得上"才认，对不上就整块放弃（避免把译文塞到错的行）
function translateLines(lines, lang) {
  var map = {}, chunks = chunkLines(lines, LYRIC_CHUNK_CHARS), idx = 0;
  var next = function () {
    if (idx >= chunks.length) return Promise.resolve(map);
    var chunk = chunks[idx++];
    return translateText(chunk.join("\n"), lang).then(function (out) {
      if (out) {
        var parts = out.split("\n");
        if (parts.length === chunk.length) {
          for (var i = 0; i < chunk.length; i++) {
            var v = String(parts[i]).trim();
            if (v !== "") map[chunk[i]] = v;
          }
        }
      }
      return next();
    });
  };
  return next();
}

/* ================================================================== */
/* 8. 参数                                                             */
/* ================================================================== */

/* 参数顺序与 kelee 参考插件一致（{${blockUpload}, ${blockShorts}, ${blockImmersive}, ${captionLang}, ${debug}}） */
var ARG_ORDER = ["blockUpload", "blockShorts", "blockImmersive", "captionLang", "debug"];

function truthy(v) {
  return v === true || v === 1 || v === "true" || v === "1" || v === "on" || v === "yes";
}

function langOf(v, fallback) {
  var s = String(v === undefined || v === null ? "" : v).trim();
  if (!/^[A-Za-z]{2,3}(-[A-Za-z0-9]{2,8})?$/.test(s)) return fallback;
  return s;
}

function parseArgs(raw) {
  var o = {}, i, s, parts;
  try {
    if (Array.isArray(raw)) {
      for (i = 0; i < ARG_ORDER.length; i++) if (raw[i] !== undefined) o[ARG_ORDER[i]] = raw[i];
    } else if (raw && typeof raw === "object") {
      o = raw;
    } else if (typeof raw === "string") {
      s = raw.trim();
      if (s.charAt(0) === "{" && s.indexOf(":") > 0) {
        o = JSON.parse(s);
      } else {
        s = s.replace(/^[\[{]\s*/, "").replace(/\s*[\]}]$/, "");
        parts = s.split(",");
        for (i = 0; i < ARG_ORDER.length && i < parts.length; i++) {
          o[ARG_ORDER[i]] = parts[i].trim().replace(/^["']|["']$/g, "");
        }
      }
    }
  } catch (e) { o = {}; }
  var capLang = langOf(o.captionLang === undefined ? DEFAULT_CAPTION_LANG : o.captionLang, "off");
  return {
    blockUpload: truthy(o.blockUpload),
    blockShorts: truthy(o.blockShorts),
    blockImmersive: truthy(o.blockImmersive),
    captionLang: capLang,
    // 歌词翻译语言：未显式传入时跟随字幕语言（字幕关掉则歌词也不翻译）
    lyricLang: langOf(o.lyricLang === undefined ? (capLang === "off" ? "off" : capLang) : o.lyricLang, "off"),
    debug: truthy(o.debug)
  };
}

/* ================================================================== */
/* 9. 分发                                                             */
/* ================================================================== */

var FEED_ENDPOINTS = { browse: 1, next: 1, search: 1 };

function transform(endpoint, body, o) {
  var ep = String(endpoint || "").toLowerCase();
  try {
    return transformInner(ep, body, o);
  } catch (e) {
    // 任何异常都退回原始字节
    return body;
  }
}

function transformInner(ep, body, o) {
  switch (ep) {
    case "player":
      return processPlayer(body, o);
    case "get_watch":
      // Watch.contents=1 -> Content{player=2, next=3}
      return edit(body, 1, function (c) {
        c = edit(c, 2, function (p) { return processPlayer(p, o); });
        c = edit(c, 3, removeAds);
        return c;
      });
    case "browse":
      return removeAds(body);
    case "next":
    case "search":
      return removeAds(body);
    case "reel/reel_watch_sequence":
    case "reel/reel_item_watch":
      return stripShortsAds(body, 0, newCtx(body));
    case "guide":
      return processGuide(body, o);
    case "account/get_setting":
      return processSettings(body);
    default:
      return body;
  }
}

function endpointOf(url) {
  var m = /youtubei\.googleapis\.com\/youtubei\/v1\/([^?]*)/i.exec(String(url || ""));
  if (!m) return "";
  return m[1].replace(/\/+$/, "");
}

function supportsLyrics(ep) {
  return ep === "browse" || ep === "player" || ep === "get_watch";
}

/* ================================================================== */
/* 10. 主流程                                                          */
/* ================================================================== */

function toBytes(body) {
  if (!body) return null;
  if (typeof body === "string") return null;                  // 文本响应不动
  if (body instanceof Uint8Array) return body;
  if (typeof ArrayBuffer !== "undefined") {
    if (body instanceof ArrayBuffer) return new Uint8Array(body);
    if (body.buffer instanceof ArrayBuffer) return new Uint8Array(body.buffer, body.byteOffset, body.byteLength);
  }
  return null;
}

function log(o, msg) {
  if (o.debug) logAlways(o, msg);
}

/* 诊断标记不受 debug 开关影响：插件参数在清缓存/更新后可能被重置为默认值，
   而这几条是"脚本有没有跑到"的唯一证据，必须始终可见。 */
function logAlways(o, msg) {
  try {
    if (typeof console !== "undefined" && console.log) console.log("[YouTubeClean] " + msg);
  } catch (e) { /* 日志失败不影响主流程 */ }
}

function run(url, body, o, finish) {
  var ep = endpointOf(url);
  if (!ep) return finish(null);
  var t0 = Date.now(), out;
  try {
    out = transform(ep, body, o);
  } catch (e) {
    logAlways(o, "protobuf_parse_failed " + ep + ": " + e);
    return finish(null);
  }

  var translated;
  if (o.lyricLang !== "off" && supportsLyrics(ep)) {
    var lines;
    try { lines = lyricLines(out); } catch (e) { lines = []; }
    if (lines.length > 0) {
      var deadline = false;
      var guard = setTimeout(function () { deadline = true; finishOnce(out); }, LYRIC_TOTAL_MS);
      translateLines(lines, o.lyricLang).then(function (map) {
        clearTimeout(guard);
        if (deadline) return;
        var finalBytes = out;
        try { finalBytes = applyLineMap(out, map); } catch (e) { finalBytes = out; }
        finishOnce(finalBytes);
      }, function () {
        clearTimeout(guard);
        if (!deadline) finishOnce(out);
      });
      return;
    }
  }
  finishOnce(out);

  function finishOnce(bytes) {
    if (bytes === body) {
      logAlways(o, "response_script_completed " + ep + " unchanged (" + (Date.now() - t0) + "ms)");
      return finish(null);
    }
    logAlways(o, "response_script_completed " + ep + " " + body.length + " -> " + bytes.length + " bytes (" + (Date.now() - t0) + "ms)");
    return finish(bytes);
  }
}

function main() {
  var o = parseArgs(typeof $argument === "undefined" ? undefined : $argument);
  var body = toBytes($response.bodyBytes || $response.body);
  logAlways(o, "response_script_entered endpoint=" + endpointOf($request.url) + " bytes=" + (body ? body.length : 0));
  if (!body || body.length < 2) {
    logAlways(o, "body_type_unsupported");
    return $done({});
  }

  var finished = false;
  var finish = function (bytes) {
    if (finished) return;
    finished = true;
    try {
      if (!bytes) return $done({});
      return $done({ body: bytes });
    } catch (e) {
      try { return $done({}); } catch (e2) { /* 放弃 */ }
    }
  };

  try {
    run($request.url, body, o, finish);
  } catch (e) {
    logAlways(o, "fatal, pass through: " + e);
    finish(null);
  }
}

if (typeof $done === "function" && typeof $response !== "undefined") {
  main();
}

if (typeof module !== "undefined" && module.exports) {
  module.exports = {
    // 线格式
    parse: parse, readVarint: readVarint, varint: varint, concat: concat,
    encodeLD: encodeLD, encodeVarintField: encodeVarintField,
    edit: edit, dropFields: dropFields, replaceRepeated: replaceRepeated,
    setVarint: setVarint, setStr: setStr, upsertMsg: upsertMsg, appendLD: appendLD,
    getRepeated: getRepeated, getStr: getStr, getStrPath: getStrPath,
    getVarint: getVarint, getVarintPath: getVarintPath, hasField: hasField,
    deepEdit: deepEdit, deepEditMulti: deepEditMulti, containsAscii: containsAscii, packedInts: packedInts,
    utf8Encode: utf8Encode, utf8Decode: utf8Decode, labelOf: labelOf,
    // 特性
    isAdBlob: isAdBlob, removeAds: removeAds, stripShortsAds: stripShortsAds,
    processPlayer: processPlayer, processGuide: processGuide, processSettings: processSettings,
    translateCaptions: translateCaptions, enablePlayability: enablePlayability,
    lyricLines: lyricLines, applyLineMap: applyLineMap, mapLyricRuns: mapLyricRuns,
    chunkLines: chunkLines, translateLines: translateLines,
    // 入口
    transform: transform, parseArgs: parseArgs, endpointOf: endpointOf,
    run: run, main: main, logAlways: logAlways
  };
}
