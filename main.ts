// Tiny stack VM (make.fun tiny stack ISA v1), implemented from ISA.md.
// For every /input/<id>: runs program.bin over input.bin and writes
// /output/<id>/stdout.bin (exact bytes) and /output/<id>/exit.txt (exit code).
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Trap codes double as exit codes.
const T_UNDER = 2, T_OVER = 3, T_DIV0 = 4, T_OPCODE = 5, T_MEM = 6,
  T_CALLS = 7, T_RET = 8, T_PC = 9, T_STEPS = 10, T_OUT = 11;

// Immediate length per opcode byte; -1 marks an unknown opcode.
const IMM = new Int8Array(256).fill(-1);
for (const [b, n] of [[0x00,0],[0x01,1],[0x02,4],[0x03,0],[0x04,0],[0x05,0],[0x06,0],[0x07,0],
  [0x10,0],[0x11,0],[0x12,0],[0x13,0],[0x14,0],[0x15,0],[0x16,0],[0x17,0],[0x18,0],[0x19,0],
  [0x1a,0],[0x1b,0],[0x1c,0],[0x1d,0],[0x1e,0],[0x20,0],[0x21,0],[0x22,0],
  [0x30,2],[0x31,2],[0x32,2],[0x33,2],[0x34,0],[0x40,0],[0x41,0],
  [0x50,0],[0x51,0],[0x52,0],[0x53,0]]) IMM[b] = n;
// Values popped / pushed per opcode byte, for the under/overflow checks.
const POPS = new Int8Array(256), PUSHES = new Int8Array(256);
for (const [b, p, q] of [[0x01,0,1],[0x02,0,1],[0x03,1,0],[0x04,1,2],[0x05,2,2],[0x06,2,3],[0x07,3,3],
  [0x10,2,1],[0x11,2,1],[0x12,2,1],[0x13,2,1],[0x14,2,1],[0x15,2,1],[0x16,2,1],[0x17,1,1],
  [0x18,2,1],[0x19,2,1],[0x1a,2,1],[0x1b,1,1],[0x1c,2,1],[0x1d,2,1],[0x1e,2,1],
  [0x20,2,1],[0x21,2,1],[0x22,2,1],[0x31,1,0],[0x32,1,0],[0x40,1,1],[0x41,2,0],
  [0x50,1,0],[0x51,1,0],[0x52,0,1],[0x53,1,0]]) { POPS[b] = p; PUSHES[b] = q; }

function runVm(prog, inp) {
  const n = prog.length;
  const st = new Int32Array(256); let sp = 0;      // data stack
  const cs = new Int32Array(64); let csp = 0;      // call stack
  const mem = new Int32Array(256);                 // memory words
  const out = new Uint8Array(65536); let olen = 0; // output bytes
  let pc = 0, steps = 0, inPos = 0;
  const finish = (code) => [out.subarray(0, olen), code];

  for (;;) {
    if (steps === 1000000) return finish(T_STEPS);
    if (pc < 0 || pc >= n) return finish(T_PC);
    const op = prog[pc];
    const imm = IMM[op];
    if (imm < 0) return finish(T_OPCODE);
    if (pc + imm >= n) return finish(T_PC); // immediate cut off by program end
    steps++;
    if (sp < POPS[op]) return finish(T_UNDER);
    if (sp - POPS[op] + PUSHES[op] > 256) return finish(T_OVER);
    const next = pc + 1 + imm;
    pc = next;
    switch (op) {
      case 0x00: return finish(0); // HALT
      case 0x01: st[sp++] = (prog[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: // PUSH32, little-endian
        st[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03: sp--; break; // POP
      case 0x04: st[sp] = st[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; } // SWAP
      case 0x06: st[sp] = st[sp - 2]; sp++; break; // OVER
      case 0x07: { // ROT: ( a b c -- b c a )
        const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; break;
      }
      case 0x17: st[sp - 1] = (-st[sp - 1]) | 0; break; // NEG
      case 0x1b: st[sp - 1] = ~st[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = st[sp - 1], a = st[sp - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { // DIV, truncated toward zero
          if (b === 0) return finish(T_DIV0);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) { // MOD, sign of a
          if (b === 0) return finish(T_DIV0);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) { // DIVU
          if (b === 0) return finish(T_DIV0);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) { // MODU
          if (b === 0) return finish(T_DIV0);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        sp -= 2; st[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, signed 16-bit offset from next
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = st[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL, unsigned 16-bit absolute target
        if (csp === 64) return finish(T_CALLS);
        cs[csp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34: // RET
        if (csp === 0) return finish(T_RET);
        pc = cs[--csp];
        break;
      case 0x40: { // LOAD
        const addr = st[sp - 1];
        if (addr < 0 || addr > 255) return finish(T_MEM);
        st[sp - 1] = mem[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        const addr = st[sp - 1], v = st[sp - 2];
        if (addr < 0 || addr > 255) return finish(T_MEM);
        sp -= 2; mem[addr] = v;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no padding or newline
        const s = String(st[sp - 1]);
        if (olen + s.length > 65536) return finish(T_OUT);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC
        if (olen + 1 > 65536) return finish(T_OUT);
        out[olen++] = st[--sp] & 255;
        break;
      case 0x52: // IN: -1 once input is used up
        st[sp++] = inPos < inp.length ? inp[inPos++] : -1;
        break;
      case 0x53: return finish(st[--sp] & 255); // EXIT
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const ent of readdirSync(I, { withFileTypes: true })) {
  if (!ent.isDirectory()) continue;
  const id = ent.name;
  const prog = readFileSync(join(I, id, 'program.bin'));
  let inp;
  try { inp = readFileSync(join(I, id, 'input.bin')); } catch { inp = Buffer.alloc(0); }
  const [bytes, code] = runVm(prog, inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), bytes);
  writeFileSync(join(O, id, 'exit.txt'), String(code) + '\n');
}
