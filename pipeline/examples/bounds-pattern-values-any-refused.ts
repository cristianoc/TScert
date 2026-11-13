// Bounds pattern P6: a fact over value locations across a call changing values.
// Fact: forall i in starts: 0 <= starts[i] < offsets.length across a callee
// whose frame is `{ values: "any"; stores: "keep" }` and which writes only a
// field of a `Cache`.
// Pretext: rich-inline.ts prepareRichInline, materializeRichInlineLineRange;
// prepare.ts getFollowingSpaceTail; han-kerning.ts getHanKerningTrims (12 sites).
// Gap: `values: "any"` covers the element cells of `starts`, and no frame
// names the kind of value locations a callee changes (fields only).
type Cache = { value: number | null };

function touch(c: Cache): Modifies<{ values: "any"; stores: "keep" }, void> {
  c.value = null;
}

/** @requires forall i in starts: safeInteger(starts[i]) && 0 <= starts[i] && starts[i] < offsets.length */
export function acrossTouch(starts: number[], offsets: Int32Array, c: Cache): number {
  let s = 0;
  /** @invariant safeInteger(k) && 0 <= k
   * @invariant forall i in starts: safeInteger(starts[i]) && 0 <= starts[i] && starts[i] < offsets.length */
  for (let k = 0; k < starts.length; k++) {
    touch(c);
    s += offsets[starts[k]!]!;
  }
  return s;
}
