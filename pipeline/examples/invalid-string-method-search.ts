// An empty needle may match at the receiver's length.
/** @requires safeInteger(r) && r < s.length */
function inside(s: string, r: number): number { return r; }
export function emptyNeedle(s: string): number {
  const r = s.lastIndexOf("");
  return inside(s, r);
}
