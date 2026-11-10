// A store separation read through a `@stable` field, `xs !== runs.open`,
// kept across an element write and a field write (`stable-first`): the
// field's location holds the array its literal put there for the record's
// life, so neither write changes which store `runs.open` reads. The loop
// writes `out[j]` and `last.at`, then calls `step` in a test, whose frame
// states the region `runs.open[*]`; the separation, stated at the loop head,
// keeps `to <= xs.length` across the call.
type Runs = { /** @stable */ readonly open: number[] };
type Last = { at: number };

function step(
  runs: Runs,
  out: number[],
): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, number> {
  runs.open.pop();
  out.push(1);
  return out.length;
}

/** @requires safeInteger(to) && 0 <= to && to <= xs.length && safeInteger(at) && 0 <= at */
export function f(xs: number[], out: number[], last: Last, to: number, at: number): number {
  const runs: Runs = { open: [] };
  let s = 0;
  /** @invariant safeInteger(i) && safeInteger(j) && safeInteger(to) && 0 <= i && to <= xs.length && xs !== runs.open */
  for (let i = 0, j = at; i < to; i++, j++) {
    if ((j & 0x7fffffff) !== j || j > out.length) throw new RangeError("index");
    out[j] = xs[i]!;
    last.at = j;
    if (s > 3 && step(runs, out) > 0) s = 0;
    s += xs[i]!;
  }
  return s;
}
