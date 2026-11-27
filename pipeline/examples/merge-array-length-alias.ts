// Branch merges emit linear equalities for every defined root term kind
// (`Store.definedKinds`): array `.length`, typed-array `.view`, and string
// `.strLength`, so an unmodified alias branch keeps `ys.length === xs.length`
// across conditional reassignment.

/** @requires safeInteger(i) && 0 <= i && i < xs.length
 *  @ensures result.length === xs.length */
export function copyOnCond(
  xs: Dense<number[]>,
  cond: boolean,
  i: number,
): Dense<number[]> {
  let ys: Dense<number[]> = xs;
  if (cond) {
    const copy = ys.slice();
    copy[i] = copy[i]! + 1;
    ys = copy;
  }
  return ys;
}

/** @requires 1 <= xs.length
 *  @ensures result.length === xs.length */
export function chainedCopies(
  xs: Dense<number[]>,
  c1: boolean,
  c2: boolean,
): Dense<number[]> {
  let ys: Dense<number[]> = xs;
  if (c1) {
    const copy = ys.slice();
    copy[copy.length - 1] = copy[copy.length - 1]! + 1;
    ys = copy;
  }
  if (c2) {
    const copy = ys.slice();
    copy[0] = copy[0]! + 2;
    ys = copy;
  }
  return ys;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length
 *  @ensures result.length === xs.length */
export function copyViewOnCond(
  xs: Uint8Array,
  cond: boolean,
  i: number,
): Uint8Array {
  let ys = xs;
  if (cond) {
    const copy = new Uint8Array(xs.length);
    copy[i] = xs[i]!;
    ys = copy;
  }
  return ys;
}

/** @requires safeInteger(i) && 0 <= i && i < text.length */
export function pickSameLengthString(
  text: string,
  other: string,
  cond: boolean,
  i: number,
): number {
  let s = text;
  if (cond && other.length === text.length) {
    s = other;
  }
  return s.codePointAt(i)!;
}
