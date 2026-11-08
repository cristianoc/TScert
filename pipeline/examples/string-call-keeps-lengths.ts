// A string method's call between a length test and the read it bounds: the
// primitive's prototype states each such method keeps the heap, so the
// fact `i < ends.length` survives `seg.charCodeAt(0)` and
// `seg.toLowerCase()` (pretext's segment walkers read a code unit, then an
// offset array, this way).

/** @requires safeInteger(i) && 0 <= i && i < ends.length */
export function codeUnitThenRead(seg: string, ends: number[], i: number): number {
  const c = seg.charCodeAt(0);
  return ends[i]! + c;
}

/** @requires safeInteger(i) && 0 <= i && i < ends.length */
export function lowerThenRead(seg: string, ends: readonly number[], i: number): number {
  const c = seg.toLowerCase();
  return ends[i]! + c.length;
}
