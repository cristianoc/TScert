// Reads in the right operand of `&&` and `||`, bounded by what the left
// operand's answer that runs it states: `true` of `a && b`, `false` of
// `a || b`, a strict equality's `false` answer an inequality.

/** @requires safeInteger(to) && to <= xs.length */
export function nonzeroPrefix(xs: number[], to: number): number {
  let e = 0;
  while (e < to && xs[e]! !== 0) e++;
  return e;
}

/** @requires safeInteger(e) */
export function positiveAt(xs: number[], e: number): boolean {
  if (e >= 0 && e < xs.length && xs[e]! > 0) return true;
  return false;
}

/** @requires safeInteger(e) */
export function outsideOrPositive(xs: number[], e: number): boolean {
  return e < 0 || e >= xs.length || xs[e]! > 0;
}

/** @requires safeInteger(e) && 0 <= e && e <= xs.length */
export function atEndOrZero(xs: number[], e: number): boolean {
  return e === xs.length || xs[e]! === 0;
}

/** @requires safeInteger(e) && 0 <= e && e <= xs.length */
export function zeroBeforeEnd(xs: number[], e: number): boolean {
  return e !== xs.length && xs[e]! === 0;
}
