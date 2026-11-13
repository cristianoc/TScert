// Bounds pattern P3, the supported neighbour of
// `bounds-pattern-fresh-field-write-refused`: the same loop with no write.
// Pretext: rich-inline.ts createLine's reads of the flow's lists.
/** @requires forall i in items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
export function noWrite(items: Int32Array, widths: number[]): number {
  let s = 0;
  for (let i = 0; i < items.length; i++) s += widths[items[i]!]!;
  return s;
}
