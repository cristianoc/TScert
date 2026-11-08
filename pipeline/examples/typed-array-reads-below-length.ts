// Reads of typed arrays below their length: `b[i]!` at `i < b.length` is the
// element, a number, by `%ByteAt%`'s bounded signature; the loop's test
// states `i < b.length`, which `%ByteLength%`'s postcondition relates to the
// typed-array length, and an element write preserves it.

export function sumBytes(b: Uint8Array): number {
  let s = 0;
  for (let i = 0; i < b.length; i++) s = s + b[i]!;
  return s;
}

export function sumDoubles(b: Float64Array): number {
  let s = 0;
  for (let i = 0; i < b.length; i++) s = s + b[i]!;
  return s;
}

// A write of each element, then a read of it back, below the length.
export function doubleEach(b: Int32Array): number {
  let last = 0;
  for (let i = 0; i < b.length; i++) {
    b[i] = b[i]! * 2;
    last = b[i]!;
  }
  return last;
}

/** @requires safeInteger(i) && 0 <= i && i < b.length */
function at(b: Uint8Array, i: number): number {
  return b[i]!;
}

export function first(b: Uint8Array): number {
  if (b.length > 0) return at(b, 0);
  return 0;
}
