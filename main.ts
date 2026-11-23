// mend-style entry for make.fun's tiny stack VM (ISA v1): runs every program in the input dir on its input
// and writes stdout.bin + exit.txt per instance. Semantics follow the kit's reference vm.mjs exactly:
// check order per step is step limit, pc range, opcode known, immediate fits, stack needs, own traps, effect.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

function run(P: Uint8Array, Q: Uint8Array): { b: Uint8Array; e: number } {
  const n = P.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const W = new Uint8Array(65536);
  let s = 0, c = 0, l = 0, q = 0, p = 0, t = 0;
  const done = (e: number) => ({ b: W.slice(0, l), e });
  const X = (e: number): never => { throw e; };
  // The checked top-of-stack memory address both LOAD and STORE need (trap 6 when out of range).
  const addr = (): number => { const a = D[s - 1]; if (a < 0 || a > 255) X(6); return a; };
  // Per-opcode metadata (known? / immediate bytes / stack pops / stack pushes), tabulated once from the
  // exact predicates the step loop used to re-derive on every step, so the hot loop is four array reads.
  const OK = new Uint8Array(256), IM = new Uint8Array(256), PO = new Uint8Array(256), PU = new Uint8Array(256);
  for (let op = 0; op < 256; op++) {
    const bin = op >= 0x10 && op <= 0x22 && op !== 0x1f;
    OK[op] = op < 8 || bin || (op >= 0x30 && op <= 0x34) || op === 0x40 || op === 0x41 || (op >= 0x50 && op <= 0x53) ? 1 : 0;
    IM[op] = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    PO[op] = op === 7 ? 3
      : op === 5 || op === 6 || op === 0x41 || (bin && op !== 0x17 && op !== 0x1b) ? 2
      : op === 3 || op === 4 || op === 0x17 || op === 0x1b || op === 0x31 || op === 0x32 || op === 0x40 || op === 0x50 || op === 0x51 || op === 0x53 ? 1 : 0;
    PU[op] = op === 6 || op === 7 ? 3
      : op === 4 || op === 5 ? 2
      : op === 1 || op === 2 || op === 0x40 || op === 0x52 || bin ? 1 : 0;
  }
  try {
    for (;;) {
      if (t === 1000000) X(10);
      if (p < 0 || p >= n) X(9);
      const op = P[p];
      if (!OK[op]) X(5);
      const im = IM[op];
      if (p + im >= n) X(9);
      t++;
      const nx = p + 1 + im;
      const po = PO[op];
      const pu = PU[op];
      if (s < po) X(2);
      if (s - po + pu > 256) X(3);
      p = nx;
      switch (op) {
        case 0x00: return done(0);
        case 0x01: D[s++] = (P[p - 1] << 24) >> 24; break;
        case 0x02: D[s++] = P[p - 4] | (P[p - 3] << 8) | (P[p - 2] << 16) | (P[p - 1] << 24); break;
        case 0x03: s--; break;
        case 0x04: D[s] = D[s - 1]; s++; break;
        case 0x05: { const v = D[s - 1]; D[s - 1] = D[s - 2]; D[s - 2] = v; break; }
        case 0x06: D[s] = D[s - 2]; s++; break;
        case 0x07: { const v = D[s - 3]; D[s - 3] = D[s - 2]; D[s - 2] = D[s - 1]; D[s - 1] = v; break; }
        case 0x17: D[s - 1] = -D[s - 1]; break;
        case 0x1b: D[s - 1] = ~D[s - 1]; break;
        case 0x30: case 0x31: case 0x32: {
          const r = ((P[p - 2] | (P[p - 1] << 8)) << 16) >> 16;
          let k = op === 0x30;
          if (op !== 0x30) { const v = D[--s]; k = op === 0x31 ? v === 0 : v !== 0; }
          if (k) p += r;
          break;
        }
        case 0x33:
          if (c === 64) X(7);
          C[c++] = p;
          p = P[p - 2] | (P[p - 1] << 8);
          break;
        case 0x34:
          if (c === 0) X(8);
          p = C[--c];
          break;
        case 0x40: D[s - 1] = M[addr()]; break;
        case 0x41: M[addr()] = D[s - 2]; s -= 2; break;
        case 0x50: {
          const v = '' + D[s - 1];
          if (l + v.length > 65536) X(11);
          for (let i = 0; i < v.length; i++) W[l++] = v.charCodeAt(i);
          s--;
          break;
        }
        case 0x51:
          if (l === 65536) X(11);
          W[l++] = D[--s] & 255;
          break;
        case 0x52: D[s++] = q < Q.length ? Q[q++] : -1; break;
        case 0x53: return done(D[--s] & 255);
        default: {
          const b = D[s - 1], a = D[s - 2];
          let r: number;
          if (op === 0x10) r = a + b | 0;
          else if (op === 0x11) r = a - b | 0;
          else if (op === 0x12) r = Math.imul(a, b);
          else if (op === 0x13) { if (!b) X(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
          else if (op === 0x14) { if (!b) X(4); r = b === -1 ? 0 : (a % b) | 0; }
          else if (op === 0x15) { if (!b) X(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
          else if (op === 0x16) { if (!b) X(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
          else if (op === 0x18) r = a & b;
          else if (op === 0x19) r = a | b;
          else if (op === 0x1a) r = a ^ b;
          else if (op === 0x1c) r = a << (b & 31);
          else if (op === 0x1d) r = a >> (b & 31);
          else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
          else if (op === 0x20) r = a === b ? 1 : 0;
          else if (op === 0x21) r = a < b ? 1 : 0;
          else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
          D[s - 2] = r;
          s--;
        }
      }
    }
  } catch (e) {
    return done(e as number);
  }
}

for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.b);
  writeFileSync(join(O, id, 'exit.txt'), r.e + '\n');
}
