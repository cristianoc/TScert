// Bounds pattern P3: a quantified fact across a write outside its array.
// Fact: forall i in items: 0 <= items[i] < widths.length, kept across
// `fragment.width = s`, a write of a field of a fresh object, whose location
// is no element of `items` and no spine of `widths`.
// Pretext: rich-inline.ts createLine (12 sites), setEmptyObjectFacts (7).
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
