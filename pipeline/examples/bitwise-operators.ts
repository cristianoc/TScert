// `&`, `|`, `^`, `<<`, `>>` and `>>>` on numbers convert their operands by
// `ToInt32` (`ToUint32` for `>>>` and every shift count), run no code, and
// give a number; their compound assignments likewise. `^` takes two bigints
// too.
export function flagSet(flags: number, flag: number): boolean {
  return (flags & flag) !== 0;
}

export function combine(a: number, b: number): number {
  let x = a & b;
  x |= 1;
  x <<= 2;
  x >>= 1;
  x >>>= 0;
  x ^= b;
  x &= 255;
  return (x ^ b) | (a >> 1) | (a >>> 3) | (b << 4);
}

export function unsigned(n: number): number {
  return n >>> 0;
}

export function bigintXor(a: bigint, b: bigint): bigint {
  return a ^ b;
}
