// png-squeeze-01-run-20261127: squeeze 1280x720 screenshots into the smallest PNG.
//
// Pipeline per image, all lossless and byte-exact:
//   1. decode the stored RGBA PNG, analyse it (opaque / grey / <=256 colours,
//      single transparent key) and build the candidate forms: palette (by
//      count and by luminance), grey / grey+alpha, RGB / RGBA, with tRNS
//      where a single transparent value can replace the alpha channel.
//   2. screen the forms and per-row filter choices (None/Sub/Up/Average/
//      Paeth, min-sum and fewest-pairs heuristics, plus per-row brute force
//      for the best forms) with zlib level 6, keeping the smallest.
//   3. compress the winner's filtered bytes with our own optimal-parsing
//      deflate in the manner of zopfli: a lazy greedy pass for statistics,
//      an entropy cost model, then two dynamic-programming parses (the second
//      reuses the first run's longest-match results), length-limited Huffman
//      codes by package-merge, adaptive block splitting, and dynamic vs
//      fixed Huffman per block, keeping the smaller.
//   4. write the PNG (IHDR / PLTE / tRNS / IDAT / IEND only).
//
// Deterministic by construction: no clock, no randomness, no environment
// reads; the work per image is fixed by its bytes, never by wall time.
// Node 22, standard library only.
import v8 from 'node:v8';
// Keep the heap (and therefore RSS) well under the harness's 512 MB cap:
// the DP workspace plus the screen's transient buffers would otherwise let
// the heap grow past 400 MB across the eight images. 320 MB of old space
// leaves room for the live set (~200 MB) while forcing timely collection.
v8.setFlagsFromString('--max-old-space-size=320');
import { copyFileSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------- deflate tables
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const LEN_SYM = new Int16Array(259);
const LEN_EXTV = new Int16Array(259);
for (let len = 3; len <= 258; len++) {
  let s = 0;
  while (s < 28 && LEN_BASE[s + 1] <= len) s++;
  LEN_SYM[len] = s;
  LEN_EXTV[len] = len - LEN_BASE[s];
}
const DIST_SYM = new Int16Array(32769);
const DIST_EXTV = new Int16Array(32769);
for (let d = 1; d <= 32768; d++) {
  let s = 0;
  while (s < 29 && DIST_BASE[s + 1] <= d) s++;
  DIST_SYM[d] = s;
  DIST_EXTV[d] = d - DIST_BASE[s];
}
const SCALE = 256; // fixed-point bits in the entropy cost model

// ---------------------------------------------------------------- PNG codec
const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();
function crc32(bytes, start, end) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}
function adler32(bytes) {
  let a = 1, b = 0;
  for (let i = 0; i < bytes.length;) {
    const e = Math.min(bytes.length, i + 5552);
    for (; i < e; i++) { a += bytes[i]; b += a; }
    a %= 65521; b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}
const ASCII = (s) => Uint8Array.from(s, (ch) => ch.charCodeAt(0));
function pngOf(chunks) {
  let size = 8;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set([137, 80, 78, 71, 13, 10, 26, 10], 0);
  let at = 8;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    out.set(ASCII(type), at + 4);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}
function ihdrOf(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}
function paeth(a, b, c) {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}
// Decode a bit-depth-8, non-interlaced PNG (colour types 0, 2, 3, 4, 6) to RGBA.
function decodePng(bytes) {
  if (bytes.length < 8 || bytes[0] !== 137 || bytes[1] !== 80 || bytes[2] !== 78 || bytes[3] !== 71) {
    throw new Error('not a PNG');
  }
  let at = 8;
  let width = 0, height = 0, colourType = 6;
  let plte = null, trns = null;
  const idat = [];
  while (at + 12 <= bytes.length) {
    const len = (bytes[at] << 24) | (bytes[at + 1] << 16) | (bytes[at + 2] << 8) | bytes[at + 3];
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    const data = bytes.subarray(at + 8, at + 8 + len);
    if (type === 'IHDR') {
      width = (data[0] << 24) | (data[1] << 16) | (data[2] << 8) | data[3];
      height = (data[4] << 24) | (data[5] << 16) | (data[6] << 8) | data[7];
      if (data[8] !== 8 || data[12] !== 0) throw new Error('unsupported PNG');
      colourType = data[9];
    } else if (type === 'PLTE') plte = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
    at += 12 + len;
  }
  const channels = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 }[colourType];
  if (!channels) throw new Error('unsupported colour type ' + colourType);
  const total = idat.reduce((a, d) => a + d.length, 0);
  const z = new Uint8Array(total);
  let off = 0;
  for (const d of idat) { z.set(d, off); off += d.length; }
  const raw = inflateSync(z);
  const stride = width * channels;
  if (raw.length !== height * (stride + 1)) throw new Error('bad PNG size');
  const rgba = new Uint8Array(width * height * 4);
  const bpp = colourType === 3 ? 1 : channels;
  for (let y = 0; y < height; y++) {
    const f = raw[y * (stride + 1)];
    const row = raw.subarray(y * (stride + 1) + 1, (y + 1) * (stride + 1));
    const prev = y === 0 ? null : raw.subarray((y - 1) * (stride + 1) + 1, y * (stride + 1));
    const out = rgba.subarray(y * width * 4, (y + 1) * width * 4);
    for (let x = 0; x < stride; x++) {
      const a = x >= bpp ? row[x - bpp] : 0;
      const b = prev === null ? 0 : prev[x];
      const c = prev !== null && x >= bpp ? prev[x - bpp] : 0;
      let v;
      if (f === 0) v = row[x];
      else if (f === 1) v = row[x] + a;
      else if (f === 2) v = row[x] + b;
      else if (f === 3) v = row[x] + ((a + b) >> 1);
      else if (f === 4) v = row[x] + paeth(a, b, c);
      else throw new Error('bad filter ' + f);
      row[x] = v & 0xff;
    }
    // convert the unfiltered row samples to RGBA
    for (let x = 0; x < width; x++) {
      const o = x * 4;
      if (colourType === 6) {
        out[o] = row[x * 4]; out[o + 1] = row[x * 4 + 1]; out[o + 2] = row[x * 4 + 2]; out[o + 3] = row[x * 4 + 3];
      } else if (colourType === 2) {
        out[o] = row[x * 3]; out[o + 1] = row[x * 3 + 1]; out[o + 2] = row[x * 3 + 2]; out[o + 3] = 255;
      } else if (colourType === 0) {
        out[o] = out[o + 1] = out[o + 2] = row[x]; out[o + 3] = 255;
      } else if (colourType === 4) {
        out[o] = out[o + 1] = out[o + 2] = row[x * 2]; out[o + 3] = row[x * 2 + 1];
      } else {
        const idx = row[x];
        out[o] = plte[idx * 3]; out[o + 1] = plte[idx * 3 + 1]; out[o + 2] = plte[idx * 3 + 2];
        out[o + 3] = trns && idx < trns.length ? trns[idx] : 255;
      }
    }
    // tRNS key for grey / RGB: a sample equal to the key is transparent
    if (trns && (colourType === 0 || colourType === 2)) {
      for (let x = 0; x < width; x++) {
        const o = x * 4;
        if (colourType === 0) {
          if (out[o] === trns[1]) out[o + 3] = 0;
        } else if (out[o] === trns[1] && out[o + 1] === trns[3] && out[o + 2] === trns[5]) {
          out[o + 3] = 0;
        }
      }
    }
  }
  return { rgba, width, height };
}

// ---------------------------------------------------------------- PNG filters
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) { out.set(cur); return; }
  if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paeth(a, b, c);
    }
  }
}
function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

// ---------------------------------------------------------------- image analysis
function analyse(rgba) {
  const n = rgba.length >>> 2;
  const u32 = new Uint32Array(rgba.buffer, rgba.byteOffset, n);
  let opaque = true, grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const c = u32[i];
      const k = counts.get(c);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(c, 1);
      } else counts.set(c, k + 1);
    }
  }
  let colours = null;
  if (!many) {
    colours = [...counts.keys()].map((c) => {
      const b = new Uint8Array(Uint32Array.of(c).buffer);
      return { rgba: [b[0], b[1], b[2], b[3]], word: c, count: counts.get(c) };
    });
  }
  return { opaque, grey, colours };
}
// The one fully transparent value (grey or RGB) the image may key by tRNS.
function transparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}
function samplesOf(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) { out[s] = rgba[d]; out[s + 1] = rgba[d + 3]; }
    else { out[s] = rgba[d]; out[s + 1] = rgba[d + 1]; out[s + 2] = rgba[d + 2]; }
  }
  return out;
}
function paletteForm(rgba, colours, order) {
  const lum = (c) => 299 * c.rgba[0] + 587 * c.rgba[1] + 114 * c.rgba[2];
  const entries = [...colours].sort((x, y) => {
    const ta = x.rgba[3] === 255 ? 1 : 0;
    const tb = y.rgba[3] === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.rgba[3] !== y.rgba[3]) return x.rgba[3] - y.rgba[3];
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.rgba[0]; plte[i * 3 + 1] = c.rgba[1]; plte[i * 3 + 2] = c.rgba[2];
    if (c.rgba[3] !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.rgba[3]);
  const n = rgba.length >>> 2;
  const u32 = new Uint32Array(rgba.buffer, rgba.byteOffset, n);
  const indices = new Uint8Array(n);
  for (let i = 0; i < n; i++) indices[i] = index.get(u32[i]);
  return { plte, trns, indices };
}
function formsOf(rgba) {
  const { opaque, grey, colours } = analyse(rgba);
  const forms = [];
  if (colours !== null) {
    for (const order of ['count', 'luminance']) {
      const p = paletteForm(rgba, colours, order);
      forms.push({
        colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns,
        filters: order === 'count' ? [0] : [0, 'minsum', 'brute'],
      });
    }
    if (!grey) return forms;
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct, trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct];
  forms.push({
    colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns,
    // No per-row brute force for RGBA: its win there is ~0.6% while the
    // brute costs ~0.5 s per image; grey/RGB keep it (grey gains ~4%).
    filters: ct === 6 ? [0, 'minsum', 'pairs'] : [0, 'minsum', 'pairs', 'brute'],
  });
  return forms;
}
const chunkBytes = (form) => (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);

// Filter one form's samples by `choice` into raw (filter byte + filtered row).
// choice: 0..4 (fixed), 'minsum' (least signed sum), 'pairs' (fewest distinct
// byte pairs), 'brute' (each row's trials compressed by zlib level 4 after the
// 32 KiB written before it, smallest kept).
function filtered(samples, width, height, bpp, choice) {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));
  const trial = Array.from({ length: 5 }, () => new Uint8Array(stride + 1));
  for (let t = 0; t < 5; t++) trial[t][0] = t;
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - 32768), at);
    let type = 0, best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t].subarray(1));
      let cost;
      if (choice === 'minsum') cost = signedSum(trial[t].subarray(1));
      else if (choice === 'pairs') {
        stamp++;
        let n = 0;
        const row = trial[t].subarray(1);
        for (let i = 1; i < row.length; i++) {
          const pair = (row[i - 1] << 8) | row[i];
          if (seen[pair] !== stamp) { seen[pair] = stamp; n++; }
        }
        cost = n;
      } else {
        cost = deflateSync(trial[t], before.length === 0
          ? { level: 4, memLevel: 9 }
          : { level: 4, memLevel: 9, dictionary: before }).length;
      }
      if (cost < best) { best = cost; type = t; }
    }
    raw[at] = type;
    filterRow(type, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
  }
  return raw;
}
const SCREEN = Object.freeze({ level: 6, memLevel: 8, strategy: 0 });
// Screen every form's non-brute choices by zlib level 6, then brute-force the
// best forms. Returns the winning {form, data} (filtered bytes).
function screen(rgba, width, height) {
  const forms = formsOf(rgba);
  let best = null;
  const perForm = [];
  for (const form of forms) {
    let fb = null;
    for (const choice of form.filters) {
      if (choice === 'brute') continue;
      const data = filtered(form.samples, width, height, form.bpp, choice);
      const z = deflateSync(data, SCREEN);
      const bytes = z.length + chunkBytes(form);
      if (fb === null || bytes < fb.bytes) fb = { form, data, choice, bytes };
    }
    perForm.push(fb);
    if (best === null || fb.bytes < best.bytes) best = fb;
  }
  perForm.sort((a, b) => a.bytes - b.bytes);
  let tried = 0;
  for (const fb of perForm) {
    if (tried >= 2) break;
    if (fb.bytes > best.bytes * 1.05) break;
    if (!fb.form.filters.includes('brute')) continue;
    tried++;
    const data = filtered(fb.form.samples, width, height, fb.form.bpp, 'brute');
    const z = deflateSync(data, SCREEN);
    const bytes = z.length + chunkBytes(fb.form);
    if (bytes < best.bytes) best = { form: fb.form, data, choice: 'brute', bytes };
    if (bytes < fb.bytes) fb.bytes = bytes;
  }
  return best;
}

// ---------------------------------------------------------------- deflate: greedy parse
// Flat symbols: a literal is one entry (0..255); a match is two entries
// (raw length + 256, i.e. 259..514, then the distance 1..32768), so the
// two kinds never collide.
function greedyParse(data, maxChain) {
  const n = data.length;
  const head = new Int32Array(32768).fill(-1);
  const prev = new Int32Array(n).fill(-1);
  const syms = [];
  const hashAt = (p) => ((data[p] << 10) ^ (data[p + 1] << 5) ^ data[p + 2]) & 32767;
  function longest(p) {
    let L = 0, D = 0;
    const h = hashAt(p);
    let cand = head[h];
    let cnt = 0;
    while (cand >= 0 && cnt++ < maxChain) {
      const dist = p - cand;
      if (dist > 32768) break;
      let len = 0;
      const max = Math.min(258, n - p);
      while (len < max && data[cand + len] === data[p + len]) len++;
      if (len > L) { L = len; D = dist; if (L >= 258) break; }
      cand = prev[cand];
    }
    return [L, D];
  }
  let i = 0;
  while (i < n) {
    if (i + 2 < n) {
      const [L, D] = longest(i);
      if (L >= 3) {
        let take = true;
        if (i + 1 < n - 2) { const [L2] = longest(i + 1); if (L2 > L + 1) take = false; }
        if (take) {
          syms.push(L + 256, D);
          for (let k = 0; k < L; k++) {
            if (i + k + 2 < n) { const h = hashAt(i + k); prev[i + k] = head[h]; head[h] = i + k; }
          }
          i += L;
          continue;
        }
      }
    }
    syms.push(data[i]);
    if (i + 2 < n) { const h = hashAt(i); prev[i] = head[h]; head[h] = i; }
    i++;
  }
  return syms;
}
function freqsOf(symbols) {
  const lf = new Int32Array(286), df = new Int32Array(30);
  lf[256] = 1;
  for (let k = 0; k < symbols.length; k++) {
    const s = symbols[k];
    if (s < 256) lf[s]++;
    else { lf[257 + LEN_SYM[s - 256]]++; df[DIST_SYM[symbols[++k]]]++; }
  }
  return { lf, df };
}
function entropyCosts(freq) {
  let total = 0;
  for (const f of freq) total += f;
  const out = new Int32Array(freq.length);
  const logT = Math.log2(total || 1);
  for (let i = 0; i < freq.length; i++) out[i] = Math.round((logT - Math.log2(Math.max(freq[i], 1))) * SCALE);
  return out;
}

// ---------------------------------------------------------------- deflate: match finder + DP
// makeMatcher builds the hash chains and the run-length array. find() returns
// the longest match and fills sublen[k] with the smallest distance reaching
// at least length k. In record mode it also stores every improving (length,
// distance) as (len<<16)|dist breakpoints for this position; in play mode it
// replays those breakpoints instead of searching, so a second DP pass costs
// almost no match finding (the zopfli "longest match cache" idea).
// One workspace per image, reused by both DP passes so the second pass
// does not allocate a second set of hash chains and DP arrays.
function makeWorkspace(d) {
  const n = d.length;
  const same = new Int32Array(n);
  same[n - 1] = 1;
  for (let i = n - 2; i >= 0; i--) same[i] = d[i] === d[i + 1] ? same[i + 1] + 1 : 1;
  return {
    same,
    head: new Int32Array(32768),
    prev: new Int32Array(n),
    sublen: new Uint16Array(259),
    cost: new Int32Array(n + 1),
    lenAt: new Uint16Array(n + 1),
    distAt: new Uint16Array(n + 1),
  };
}
function makeMatcher(d, cache, ws) {
  const n = d.length;
  const { same, head, prev, sublen } = ws;
  head.fill(-1);
  const hashAt = (p) => ((d[p] << 10) ^ (d[p + 1] << 5) ^ d[p + 2]) & 32767;
  function insert(p) { const h = hashAt(p); prev[p] = head[h]; head[h] = p; }
  function find(i, maxChain, good, tierMin) {
    const limit = Math.min(258, n - i);
    if (limit < 3) return [0, 0];
    if (cache && cache.mode === 'play') {
      const off = cache.off[i], c = cache.cnt[i];
      let best = 0, bestDist = 0, prevLen = 0;
      for (let j = 0; j < c; j++) {
        const rec = cache.flat[off + j];
        const len = rec >>> 16, dist = rec & 0xffff;
        for (let k = prevLen + 1; k <= len; k++) sublen[k] = dist;
        prevLen = len; best = len; bestDist = dist;
      }
      return [best, bestDist];
    }
    const h = hashAt(i);
    let cand = head[h];
    let best = 0, bestDist = 0;
    const same0 = same[i];
    const ptr0 = cache ? cache.ptr : 0;
    if (cache) cache.off[i] = ptr0;
    // Two-tier search: a short first pass finds the good matches that live
    // nearby (the common case); only when nothing decent turned up do we
    // spend the full chain budget, where a far match is worth far more than
    // literals. Near-deep-chain compression at near-shallow-chain cost.
    const TIER1 = 256, TIER_MIN = tierMin;
    let budget = Math.min(TIER1, maxChain);
    let walked = 0;
    while (cand >= 0) {
      if (walked >= budget) {
        if (best < TIER_MIN && budget < maxChain) budget = maxChain;
        else break;
      }
      walked++;
      const dist = i - cand;
      if (dist > 32768) break;
      if (best === 0 || d[cand + best] === d[i + best]) {
        let len = 0;
        if (same0 > 2 && d[cand] === d[i]) {
          const s1 = same[cand];
          len = same0 < s1 ? same0 : s1;
          if (len > limit) len = limit;
        }
        while (len < limit && d[cand + len] === d[i + len]) len++;
        if (len > best) {
          for (let j = best + 1; j <= len; j++) sublen[j] = dist;
          best = len; bestDist = dist;
          if (cache) {
            if (cache.ptr >= cache.flat.length) {
              const nf = new Int32Array(cache.flat.length * 2);
              nf.set(cache.flat);
              cache.flat = nf;
            }
            cache.flat[cache.ptr++] = (len << 16) | dist;
          }
          if (best >= limit) break;
          if (best >= good) budget = walked + ((budget - walked) >> 2);
        }
      }
      cand = prev[cand];
    }
    if (cache) cache.cnt[i] = cache.ptr - ptr0;
    return [best, bestDist];
  }
  return { same, insert, find, sublen };
}
function dpParse(d, llEnt, dEnt, maxChain, cache, good, ws, tierMin) {
  const n = d.length;
  const INF = 1 << 30;
  const cost = ws.cost.fill(INF);
  cost[0] = 0;
  const lenAt = ws.lenAt.fill(0); // 1 = literal, k = match length, 0 = unreachable
  const distAt = ws.distAt.fill(0);
  const { same, insert, find, sublen } = makeMatcher(d, cache, ws);
  const lenCost = new Int32Array(259);
  for (let k = 3; k <= 258; k++) lenCost[k] = llEnt[257 + LEN_SYM[k]] + LEN_EXTRA[LEN_SYM[k]] * SCALE;
  let minDistCost = Infinity;
  const distCostArr = new Int32Array(32769);
  for (let dd = 1; dd <= 32768; dd++) {
    const c = dEnt[DIST_SYM[dd]] + DIST_EXTRA[DIST_SYM[dd]] * SCALE;
    distCostArr[dd] = c;
    if (c < minDistCost) minDistCost = c;
  }
  let minMatchCost = Infinity;
  for (let k = 3; k <= 258; k++) { const c = lenCost[k] + minDistCost; if (c < minMatchCost) minMatchCost = c; }
  const matchCost258d1 = lenCost[258] + distCostArr[1];
  let i = 0;
  while (i < n) {
    // long-repetition shortcut (zopfli): inside a run >516, emit dist-1 x258
    if (same[i] > 516 && i > 259 && i + 517 < n && same[i - 258] > 258) {
      const target = i + 258;
      const nc = cost[i] + matchCost258d1;
      if (nc < cost[target]) { cost[target] = nc; lenAt[target] = 258; distAt[target] = 1; }
      for (let k = 0; k < 258; k++) insert(i + k);
      i = target;
      continue;
    }
    const c = cost[i];
    const nc = c + llEnt[d[i]];
    if (nc < cost[i + 1]) { cost[i + 1] = nc; lenAt[i + 1] = 1; }
    if (i + 2 < n) {
      const [best] = find(i, maxChain, good, tierMin);
      const kend = Math.min(best, n - i);
      const base = c;
      for (let k = 3; k <= kend; k++) {
        if (cost[i + k] <= minMatchCost + base) continue;
        const nc2 = base + lenCost[k] + distCostArr[sublen[k]];
        if (nc2 < cost[i + k]) { cost[i + k] = nc2; lenAt[i + k] = k; distAt[i + k] = sublen[k]; }
      }
      insert(i);
    }
    i++;
  }
  const rev = [];
  let p = n;
  while (p > 0) {
    const l = lenAt[p];
    if (l === 0) throw new Error('unreachable position ' + p);
    if (l === 1) rev.push([d[p - 1]]);
    else rev.push([l + 256, distAt[p]]);
    p -= l;
  }
  const out = [];
  for (let k = rev.length - 1; k >= 0; k--) {
    const s = rev[k];
    out.push(s[0]);
    if (s.length === 2) out.push(s[1]);
  }
  return out;
}
// ---------------------------------------------------------------- deflate: package-merge Huffman
// Length-limited Huffman code lengths by package-merge (Wikipedia's
// description). Verified against brute-force optima in work/pm.mjs: the
// lengths satisfy Kraft = 1 with max <= limit and minimise sum(freq * len).
function pmLengths(freq, L) {
  const n = freq.length;
  const syms = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) syms.push(i);
  const out = new Uint8Array(n);
  if (syms.length === 0) return out;
  if (syms.length === 1) { out[syms[0]] = 1; return out; }
  if (syms.length === 2) { out[syms[0]] = 1; out[syms[1]] = 1; return out; }
  let cur = syms.map((s) => ({ v: freq[s], s: [s] }));
  cur.sort((a, b) => a.v - b.v);
  for (let level = 0; level < L; level++) {
    const packaged = [];
    for (let j = 0; j + 1 < cur.length; j += 2) {
      packaged.push({ v: cur[j].v + cur[j + 1].v, s: cur[j].s.concat(cur[j + 1].s) });
    }
    if (level === L - 1) { cur = packaged; break; }
    const next = syms.map((s) => ({ v: freq[s], s: [s] }));
    cur = packaged.concat(next);
    cur.sort((a, b) => a.v - b.v);
  }
  cur.sort((a, b) => a.v - b.v);
  const take = Math.min(syms.length - 1, cur.length);
  for (let i = 0; i < take; i++) for (const s of cur[i].s) out[s]++;
  return out;
}

// ---------------------------------------------------------------- deflate: Huffman codes + bit writer
function revBits(code, len) {
  let r = 0;
  for (let i = 0; i < len; i++) { r = (r << 1) | (code & 1); code >>= 1; }
  return r;
}
function buildCodes(lengths) {
  let maxL = 0;
  for (const l of lengths) if (l > maxL) maxL = l;
  const bl = new Int32Array(maxL + 1);
  for (const l of lengths) if (l) bl[l]++;
  const next = new Int32Array(maxL + 1);
  let code = 0;
  for (let b = 1; b <= maxL; b++) { code = (code + bl[b - 1]) << 1; next[b] = code; }
  const codes = new Int32Array(lengths.length);
  for (let s = 0; s < lengths.length; s++) {
    const l = lengths[s];
    if (l) codes[s] = revBits(next[l]++, l);
  }
  return codes;
}
class BitW {
  constructor() { this.bytes = []; this.acc = 0; this.nbits = 0; }
  put(code, len) {
    this.acc |= (code & ((1 << len) - 1)) << this.nbits;
    this.nbits += len;
    while (this.nbits >= 8) { this.bytes.push(this.acc & 255); this.acc >>>= 8; this.nbits -= 8; }
  }
  finish() {
    if (this.nbits > 0) this.bytes.push(this.acc & 255);
    return Uint8Array.from(this.bytes);
  }
}
const FIXED_LIT = new Uint8Array(288);
{
  for (let i = 0; i < 144; i++) FIXED_LIT[i] = 8;
  for (let i = 144; i < 256; i++) FIXED_LIT[i] = 9;
  for (let i = 256; i < 280; i++) FIXED_LIT[i] = 7;
  for (let i = 280; i < 288; i++) FIXED_LIT[i] = 8;
}
const FIXED_DIST = new Uint8Array(30).fill(5);

// The dynamic-block header for given literal/length code lengths: the
// code-length code, its tokens, and the header's bit cost. Shared by the
// block splitter (which only counts bits) and the writer (which writes them).
function dynamicBlockParts(litLen, distLen) {
  let hlit = 286, hdist = 30;
  while (hlit > 257 && litLen[hlit - 1] === 0) hlit--;
  while (hdist > 1 && distLen[hdist - 1] === 0) hdist--;
  const seq = [];
  for (let s = 0; s < hlit; s++) seq.push(litLen[s]);
  for (let s = 0; s < hdist; s++) seq.push(distLen[s]);
  const clFreq = new Int32Array(19);
  const tokens = [];
  let i = 0;
  const tot = hlit + hdist;
  while (i < tot) {
    const v = seq[i];
    let run = 1;
    while (i + run < tot && seq[i + run] === v) run++;
    if (v === 0) {
      let r = run;
      while (r >= 11) { const take = Math.min(r, 138); tokens.push([18, take - 11]); clFreq[18]++; r -= take; }
      if (r >= 3) { tokens.push([17, r - 3]); clFreq[17]++; r = 0; }
      while (r > 0) { tokens.push([0, 0]); clFreq[0]++; r--; }
    } else {
      tokens.push([v, 0]); clFreq[v]++;
      let r = run - 1;
      while (r >= 3) { const take = Math.min(r, 6); tokens.push([16, take - 3]); clFreq[16]++; r -= take; }
      while (r > 0) { tokens.push([v, 0]); clFreq[v]++; r--; }
    }
    i += run;
  }
  const clLen = pmLengths(clFreq, 7);
  const clCode = buildCodes(clLen);
  const order = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
  let hclen = 19;
  while (hclen > 4 && clLen[order[hclen - 1]] === 0) hclen--;
  let headerBits = 3 + 5 + 5 + 4 + 3 * hclen;
  for (const [t, ex] of tokens) {
    headerBits += clLen[t];
    if (t === 16) headerBits += 2;
    else if (t === 17) headerBits += 3;
    else if (t === 18) headerBits += 7;
  }
  return { hlit, hdist, hclen, tokens, clLen, clCode, order, headerBits };
}
function freqsOfRange(symbols, lo, hi) {
  const lf = new Int32Array(286), df = new Int32Array(30);
  lf[256] = 1;
  for (let k = lo; k < hi; k++) {
    const s = symbols[k];
    if (s < 256) lf[s]++;
    else { lf[257 + LEN_SYM[s - 256]]++; df[DIST_SYM[symbols[++k]]]++; }
  }
  return { lf, df };
}
// Estimated bit cost of one deflate block holding flat symbols [lo, hi):
// data bits under its own best Huffman code plus the block header, dynamic
// vs fixed, whichever is smaller.
function segmentCost(symbols, lo, hi) {
  const { lf, df } = freqsOfRange(symbols, lo, hi);
  const litLen = pmLengths(lf, 15);
  let distLen = pmLengths(df, 15);
  if (!distLen.some((x) => x)) distLen[0] = 1;
  let dynBits = dynamicBlockParts(litLen, distLen).headerBits;
  for (let s = 0; s < 286; s++) dynBits += lf[s] * litLen[s];
  for (let s = 0; s < 30; s++) dynBits += df[s] * distLen[s];
  let fixBits = 3;
  for (let s = 0; s < 286; s++) fixBits += lf[s] * FIXED_LIT[s];
  for (let s = 0; s < 30; s++) fixBits += df[s] * FIXED_DIST[s];
  if (fixBits <= dynBits) return { bits: fixBits, fixed: true, litLen: null, distLen: null };
  return { bits: dynBits, fixed: false, litLen, distLen };
}
function symbolStarts(symbols) {
  const starts = [0];
  for (let k = 0; k < symbols.length;) {
    const s = symbols[k++];
    if (s >= 256) k++;
    starts.push(k);
  }
  return Int32Array.from(starts);
}
// Split the symbol stream into blocks where separate Huffman tables pay for
// themselves: try 1/4, 1/2, 3/4 splits, recurse while a split saves bits.
function splitBlocks(symbols, starts) {
  const nsym = starts.length - 1;
  const segments = [];
  function rec(a, b, depth) {
    if (b - a < 4000 || depth >= 2) {
      segments.push({ a, b, lo: starts[a], hi: starts[b], info: segmentCost(symbols, starts[a], starts[b]) });
      return;
    }
    const whole = segmentCost(symbols, starts[a], starts[b]);
    let bestSave = 0, bestMid = -1;
    for (const f of [0.25, 0.5, 0.75]) {
      const mid = a + Math.max(1, Math.floor((b - a) * f));
      if (mid <= a || mid >= b) continue;
      const left = segmentCost(symbols, starts[a], starts[mid]);
      const right = segmentCost(symbols, starts[mid], starts[b]);
      const save = whole.bits - left.bits - right.bits;
      if (save > bestSave) { bestSave = save; bestMid = mid; }
    }
    if (bestMid < 0) {
      segments.push({ a, b, lo: starts[a], hi: starts[b], info: whole });
      return;
    }
    rec(a, bestMid, depth + 1);
    rec(bestMid, b, depth + 1);
  }
  rec(0, nsym, 0);
  return segments;
}
function writeSymbols(w, symbols, lo, hi, litCode, distCode, litLen, distLen) {
  for (let k = lo; k < hi;) {
    const s = symbols[k++];
    if (s < 256) w.put(litCode[s], litLen[s]);
    else {
      const len = s - 256;
      const ls = 257 + LEN_SYM[len];
      w.put(litCode[ls], litLen[ls]);
      w.put(LEN_EXTV[len], LEN_EXTRA[ls - 257]);
      const dist = symbols[k++];
      const ds = DIST_SYM[dist];
      w.put(distCode[ds], distLen[ds]);
      w.put(DIST_EXTV[dist], DIST_EXTRA[ds]);
    }
  }
  w.put(litCode[256], litLen[256]);
}
function emitZlib(data, symbols, segments) {
  const w = new BitW();
  for (let b = 0; b < segments.length; b++) {
    const seg = segments[b];
    const final = b === segments.length - 1;
    if (seg.info.fixed) {
      const litCode = buildCodes(FIXED_LIT), distCode = buildCodes(FIXED_DIST);
      w.put(final ? 1 : 0, 1);
      w.put(1, 2);
      writeSymbols(w, symbols, seg.lo, seg.hi, litCode, distCode, FIXED_LIT, FIXED_DIST);
    } else {
      const parts = dynamicBlockParts(seg.info.litLen, seg.info.distLen);
      const litCode = buildCodes(seg.info.litLen), distCode = buildCodes(seg.info.distLen);
      w.put(final ? 1 : 0, 1);
      w.put(2, 2);
      w.put(parts.hlit - 257, 5);
      w.put(parts.hdist - 1, 5);
      w.put(parts.hclen - 4, 4);
      for (let k = 0; k < parts.hclen; k++) w.put(parts.clLen[parts.order[k]], 3);
      for (const [t, ex] of parts.tokens) {
        w.put(parts.clCode[t], parts.clLen[t]);
        if (t === 16) w.put(ex, 2);
        else if (t === 17) w.put(ex, 3);
        else if (t === 18) w.put(ex, 7);
      }
      writeSymbols(w, symbols, seg.lo, seg.hi, litCode, distCode, seg.info.litLen, seg.info.distLen);
    }
  }
  const body = w.finish();
  const adler = adler32(data);
  const out = new Uint8Array(2 + body.length + 4);
  out[0] = 0x78; out[1] = 0xda;
  out.set(body, 2);
  out[2 + body.length] = (adler >>> 24) & 255;
  out[3 + body.length] = (adler >>> 16) & 255;
  out[4 + body.length] = (adler >>> 8) & 255;
  out[5 + body.length] = adler & 255;
  return out;
}

// ---------------------------------------------------------------- image pipeline
function compressImage(rgba, width, height) {
  const best = screen(rgba, width, height);
  const data = best.data;
  const form = best.form;
  let syms = greedyParse(data, 128);
  let { lf, df } = freqsOf(syms);
  let llEnt = entropyCosts(lf), dEnt = entropyCosts(df);
  const ws = makeWorkspace(data);
  const cache = {
    mode: 'record',
    flat: new Int32Array(data.length * 3),
    off: new Int32Array(data.length + 1),
    cnt: new Uint8Array(data.length),
    ptr: 0,
  };
  // Palette data is small and repetitive: deep chains find its far matches.
  // RGBA data is the biggest and slowest, and barely gains from deep chains.
  const chain = form.colourType === 3 ? 1024 : 512;
  const good = form.colourType === 3 ? 258 : 128;
  // Palette data is 1 byte/px and its long matches live far down the chain,
  // so it keeps the full deep walk; channel data stops early on a decent
  // match, which is where the two-tier search earns its time.
  const tierMin = form.colourType === 3 ? 258 : 16;
  syms = dpParse(data, llEnt, dEnt, chain, cache, good, ws, tierMin);
  // Second pass only for 1-byte forms (palette/grey): for RGB/RGBA it costs
  // ~1-2 s per image for ~1.4% and is the first thing to go under the 60 s cap.
  if (form.bpp < 3) {
    ({ lf, df } = freqsOf(syms));
    llEnt = entropyCosts(lf); dEnt = entropyCosts(df);
    cache.mode = 'play';
    syms = dpParse(data, llEnt, dEnt, chain, cache, good, ws, tierMin);
  }
  const starts = symbolStarts(syms);
  const segments = splitBlocks(syms, starts);
  const z = emitZlib(data, syms, segments);
  const chunks = [['IHDR', ihdrOf(width, height, form.colourType)]];
  if (form.plte) chunks.push(['PLTE', form.plte]);
  if (form.trns) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', z]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngOf(chunks);
}

// ---------------------------------------------------------------- driver
const INPUT = process.env.MAKEFUN_INPUT_DIR || '/input';
const OUTPUT = process.env.MAKEFUN_OUTPUT_DIR || '/output';
function main() {
  const ids = readdirSync(INPUT).filter((x) => /^[a-z]\d{3}$/.test(x)).sort();
  for (const id of ids) {
    const inFile = join(INPUT, id, 'image.png');
    const outDir = join(OUTPUT, id);
    mkdirSync(outDir, { recursive: true });
    const outFile = join(outDir, 'image.png');
    try {
      const bytes = readFileSync(inFile);
      const { rgba, width, height } = decodePng(bytes);
      const png = compressImage(rgba, width, height);
      writeFileSync(outFile, png);
    } catch (e) {
      // never leave an instance unanswered: copy the input (a valid PNG)
      try { copyFileSync(inFile, outFile); } catch { /* nothing left to do */ }
      console.error(id, 'fallback copy:', e.message);
    }
  }
}
main();
