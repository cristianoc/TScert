// Bounds pattern P3: a quantified fact across a write outside its array.
// Fact: forall i in items: 0 <= items[i] < widths.length, kept across
// `fragment.width = s`, a write of a field of a fresh object, whose location
// is no element of `items` and no store of `widths`.
// Pretext: rich-inline.ts createLine (12 sites), setEmptyObjectFacts (7).
// Gap: a quantified fact is kept across a field write only where the written
// value meets its body; the field's region being apart from the fact's
// support is not used, with the fact a precondition or a loop invariant.
type Fragment = { item: number; width: number };

/** @requires forall i in items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
export function acrossWrite(items: Int32Array, widths: number[]): number {
  const fragment: Fragment = { item: 0, width: 0 };
  let s = 0;
  for (let i = 0; i < items.length; i++) {
    fragment.width = s;
    s += widths[items[i]!]!;
  }
  return s + fragment.width;
}

/** @requires forall i in items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
export function acrossWriteInvariant(items: Int32Array, widths: number[]): number {
  const fragment: Fragment = { item: 0, width: 0 };
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i
   * @invariant forall k in items: safeInteger(items[k]) && 0 <= items[k] && items[k] < widths.length */
  for (let i = 0; i < items.length; i++) {
    fragment.width = i;
    s += widths[items[i]!]!;
  }
  return s + fragment.width;
}
