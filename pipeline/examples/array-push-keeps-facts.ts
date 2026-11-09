// `Array.prototype.push` on an ordinary array changes no old location but its
// receiver's store, which it grows (SOURCE-CONTRACTS.md, "Native
// footprints"; ARITHMETIC.md, "Linear facts", `receiverGrows`): a push
// preserves every fact over values, paths and typed-array lengths, and every fact
// whose lengths have coefficients at most 0, the lower bounds of lengths.

export type Prepared = {
  segmentFlags: Uint8Array;
  widths: number[];
  count: number;
};

// pretext's shape: a fresh array filled in a loop bounded by a view read
// through a field; `i < p.segmentFlags.length` survives each push, so `i++`
// is a safe integer.
export function flagsOf(p: Prepared): number {
  const out: number[] = [];
  for (let i = 0; i < p.segmentFlags.length; i++) out.push(p.segmentFlags[i]!);
  return out.length;
}

// A parameter's path facts across a push to a fresh array.
/** @requires safeInteger(p.count) && 0 <= p.count && p.count < p.widths.length */
export function widthAfterPush(p: Prepared): number {
  const out: number[] = [];
  out.push(1);
  const c = p.count;
  return p.widths[c]! + out.length;
}

// `0 <= i < other.length` across a push to an array that may be `other`
// itself: the push only grows a length.
/** @requires safeInteger(i) && 0 <= i && i < other.length */
export function readAfterPush(
  out: number[],
  other: number[],
  i: number,
): number {
  out.push(0);
  return other[i]!;
}
