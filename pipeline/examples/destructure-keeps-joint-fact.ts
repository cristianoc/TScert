// A fact relating two fields, `a.flags.length <= a.starts.length`, read
// through one object pattern: each field's read is restated of its name in
// the pattern's order, so the fact is stated of `flags` and `starts`
// together, and `i < flags.length` bounds the read of `starts` (pretext's
// line walkers destructure their prepared text this way).
type A = { starts: number[]; flags: number[] };

/** @requires safeInteger(i) && 0 <= i && a.flags.length <= a.starts.length */
export function destructured(a: A, i: number): number {
  const { starts, flags } = a;
  return i < flags.length ? starts[i]! : 0;
}
