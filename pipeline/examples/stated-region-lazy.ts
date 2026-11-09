// Fresh array storage in a regional body (FOOTPRINTS.md, "Fresh array
// storage"): `take` writes `acc`, so `acc` is a cell, `null` until the first
// long string allocates its array. The cell's contents are a fresh value at
// every point: `null` meets it, the array literal allocates a store past the
// entry heap, and no step of the loop changes a location of class value. So
// the store `push` grows at `(acc ??= [])` is none of the entry heap's,
// rebased to no region; `runs.open` is the region the frame names.
type Runs = { /** @stable */ readonly open: number[] };

export function longer(runs: Runs, xs: string[]): Modifies<{ values: "any"; "runs.open[*]": "any" }, string[] | null> {
  let acc: string[] | null = null;
  const take = (): string[] | null => {
    const out = acc;
    acc = null;
    return out;
  };
  for (let i = 0; i < xs.length; i++) {
    const s = xs[i]!;
    if (s.length > 1) (acc ??= []).push(s);
  }
  runs.open.push(xs.length);
  return take();
}
