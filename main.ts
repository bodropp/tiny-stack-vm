// tiny-stack-vm: a correct interpreter for make.fun's tiny stack ISA v1.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const M = new Int8Array(256).fill(-1), U = new Int8Array(256), V = new Int8Array(256);
[[0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0], [4, 0, 1, 2], [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3], [0x17, 0, 1, 1], [0x1b, 0, 1, 1], [0x30, 2, 0, 0], [0x31, 2, 1, 0], [0x32, 2, 1, 0], [0x33, 2, 0, 0], [0x34, 0, 0, 0], [0x40, 0, 1, 1], [0x41, 0, 2, 0], [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1], [0x53, 0, 1, 0]].forEach(t => { M[t[0]] = t[1]; U[t[0]] = t[2]; V[t[0]] = t[3]; });
for (let o = 0x10; o <= 0x16; o++) { M[o] = 0; U[o] = 2; V[o] = 1; }
for (let o = 0x18; o <= 0x1a; o++) { M[o] = 0; U[o] = 2; V[o] = 1; }
for (let o = 0x1c; o <= 0x1e; o++) { M[o] = 0; U[o] = 2; V[o] = 1; }
for (let o = 0x20; o <= 0x22; o++) { M[o] = 0; U[o] = 2; V[o] = 1; }
const F = {
  0x10: (a, b) => a + b | 0,
  0x11: (a, b) => a - b | 0,
  0x12: (a, b) => Math.imul(a, b),
  0x13: (a, b) => a === -2147483648 && b === -1 ? a : a / b | 0,
  0x14: (a, b) => b === -1 ? 0 : a % b | 0,
  0x15: (a, b) => Math.floor((a >>> 0) / (b >>> 0)) | 0,
  0x16: (a, b) => (a >>> 0) % (b >>> 0) | 0,
  0x18: (a, b) => a & b,
  0x19: (a, b) => a | b,
  0x1a: (a, b) => a ^ b,
  0x1c: (a, b) => a << (b & 31),
  0x1d: (a, b) => a >> (b & 31),
  0x1e: (a, b) => a >>> (b & 31) | 0,
  0x20: (a, b) => a === b ? 1 : 0,
  0x21: (a, b) => a < b ? 1 : 0,
  0x22: (a, b) => (a >>> 0) < (b >>> 0) ? 1 : 0,
};
const E = new TextEncoder();
function R(p, q) {
  const n = p.length, D = new Int32Array(256), C = new Int32Array(64), m = new Int32Array(256), o = new Uint8Array(65536);
  let s = 0, c = 0, l = 0, i = 0, pc = 0, t = 0;
  const d = x => ({ out: o.slice(0, l), code: x });
  for (;;) {
    if (t === 1e6) return d(10);
    if (pc < 0 || pc >= n) return d(9);
    const k = p[pc], w = M[k];
    if (w < 0) return d(5);
    if (pc + w >= n) return d(9);
    t++;
    const nx = pc + 1 + w, u = U[k];
    if (s < u) return d(2);
    if (s - u + V[k] > 256) return d(3);
    pc = nx;
    if (k >= 0x10 && k <= 0x22 && k !== 0x17 && k !== 0x1b && F[k]) {
      const b = D[s - 1], a = D[s - 2];
      if ((k === 0x13 || k === 0x14 || k === 0x15 || k === 0x16) && b === 0) return d(4);
      s -= 2;
      D[s++] = F[k](a, b);
      continue;
    }
    switch (k) {
      case 0: return d(0);
      case 1: D[s++] = p[nx - 1] << 24 >> 24; break;
      case 2: D[s++] = p[nx - 4] | p[nx - 3] << 8 | p[nx - 2] << 16 | p[nx - 1] << 24; break;
      case 3: s--; break;
      case 4: D[s] = D[s - 1]; s++; break;
      case 5: { const g = D[s - 1]; D[s - 1] = D[s - 2]; D[s - 2] = g; break; }
      case 6: D[s] = D[s - 2]; s++; break;
      case 7: { const a = D[s - 3]; D[s - 3] = D[s - 2]; D[s - 2] = D[s - 1]; D[s - 1] = a; break; }
      case 0x17: D[s - 1] = -D[s - 1] | 0; break;
      case 0x1b: D[s - 1] = ~D[s - 1]; break;
      case 0x30: case 0x31: case 0x32: {
        const r = (p[nx - 2] | p[nx - 1] << 8) << 16 >> 16;
        let y = true;
        if (k !== 0x30) { const v = D[--s]; y = k === 0x31 ? v === 0 : v !== 0; }
        if (y) pc = nx + r;
        break;
      }
      case 0x33:
        if (c === 64) return d(7);
        C[c++] = nx;
        pc = p[nx - 2] | p[nx - 1] << 8;
        break;
      case 0x34:
        if (c === 0) return d(8);
        pc = C[--c];
        break;
      case 0x40: {
        const a = D[s - 1];
        if (a < 0 || a >= 256) return d(6);
        D[s - 1] = m[a];
        break;
      }
      case 0x41: {
        const a = D[s - 1], v = D[s - 2];
        if (a < 0 || a >= 256) return d(6);
        s -= 2;
        m[a] = v;
        break;
      }
      case 0x50: {
        const b = E.encode(String(D[s - 1]));
        if (l + b.length > 65536) return d(11);
        s--;
        o.set(b, l);
        l += b.length;
        break;
      }
      case 0x51:
        if (l + 1 > 65536) return d(11);
        o[l++] = D[--s] & 255;
        break;
      case 0x52: D[s++] = i < q.length ? q[i++] : -1; break;
      case 0x53: return d(D[--s] & 255);
      default: return d(5);
    }
  }
}
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = R(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), r.code + '\n');
}
