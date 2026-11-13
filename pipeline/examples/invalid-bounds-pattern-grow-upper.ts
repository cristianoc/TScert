// Bounds pattern P4, the unsafe neighbour of
// `bounds-pattern-grow-upper-refused`: with no separation stated and a frame
// growing every store, `out` may be a.flags, whose growth breaks the upper
// bound a.flags.length <= a.starts.length (run under Node with out = a.flags:
// NaN).
export type Analysis = {
  /** @stable */ readonly starts: number[];
  /** @stable */ readonly flags: number[];
};

function note(out: number[], v: number): Modifies<{ values: "any"; stores: "grow" }, void> {
  out.push(v);
}

/** @requires a.flags.length === a.starts.length */
export function aliased(a: Analysis, out: number[]): number {
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && a.flags.length <= a.starts.length */
  for (let i = 0; i < 4 && i + 1 < a.flags.length; i++) {
    note(out, i);
    s += a.starts[i + 1]!;
  }
  return s;
}
