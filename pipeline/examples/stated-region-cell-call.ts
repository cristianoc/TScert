// Fresh array storage in a cell across a call (FOOTPRINTS.md, "Fresh array
// storage"): `take` writes `acc`, so `acc` is a cell, and `note`'s frame
// states `values: "any"`, which may replace the cell's contents with an
// old array. The cell keeps its freshness only across steps whose frames
// keep every location of class value, so the store `push` grows after the
// call is any of the entry heap's, refused at the regional check. `note`
// cannot reach the cell, but the frame states no reachability; the slot
// form, `stated-slot-collect`, verifies.
type Runs = { /** @stable */ readonly open: number[] };

function note(runs: Runs, n: number): Modifies<{ values: "any"; "runs.open[*]": "any" }, void> {
  runs.open.push(n);
}

export function longer(runs: Runs, xs: string[]): Modifies<{ values: "any"; "runs.open[*]": "any" }, string[] | null> {
  let acc: string[] | null = null;
  const take = (): string[] | null => {
    const out = acc;
    acc = null;
    return out;
  };
  for (let i = 0; i < xs.length; i++) {
    const s = xs[i]!;
    note(runs, s.length);
    (acc ??= []).push(s);
  }
  return take();
}
