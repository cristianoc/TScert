// A loop invariant (PROGRAM-TYPING.md, "Loop invariants"): `@invariant C`
// before a loop states `C` at its head, which every entry to the head
// establishes and the body may assume. `j <= 2 * i` relates two counters
// stepping by 2 and by 1, a form no fact of the loop's entry names, so the
// producer's own facts do not state it; with it, `ys[j]!` reads below the
// length.

/** @requires 2 * xs.length <= ys.length */
export function everyOther(xs: number[], ys: number[]): number {
  let j = 0;
  let s = 0;
  /** @invariant safeInteger(i) && safeInteger(j) && 0 <= j && j <= 2 * i */
  for (let i = 0; i < xs.length; i++) {
    s += xs[i]! * ys[j]!;
    j += 2;
  }
  return s;
}
