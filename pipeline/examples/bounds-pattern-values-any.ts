// Bounds pattern P6, the supported neighbour of
// `bounds-pattern-values-any-refused`: a callee of frame `{ values: "init";
// stores: "keep" }`, which changes no location holding a number.
// Pretext: the measuring caches of measurement.ts.
type Cache = { value: number | null };

function warm(c: Cache): Modifies<{ values: "init"; stores: "keep" }, void> {
  c.value ??= 5;
}

/** @requires forall i in starts: safeInteger(starts[i]) && 0 <= starts[i] && starts[i] < offsets.length */
export function acrossWarm(starts: number[], offsets: Int32Array, c: Cache): number {
  let s = 0;
  /** @invariant safeInteger(k) && 0 <= k
   * @invariant forall i in starts: safeInteger(starts[i]) && 0 <= starts[i] && starts[i] < offsets.length */
  for (let k = 0; k < starts.length; k++) {
    warm(c);
    s += offsets[starts[k]!]!;
  }
  return s;
}
