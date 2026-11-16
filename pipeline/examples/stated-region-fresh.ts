// Fresh array storage in a regional body (FOOTPRINTS.md, "Fresh array
// storage"): `out` is allocated by the body, so its spine lies at or above
// the entry heap's length on every iteration of the loop, and the spine
// `out.push(i)` grows is none of the entry heap's, rebased to no region.
// `runs.open.push(n)` changes the spine the frame names.
type Runs = { /** @stable */ readonly open: number[] };
export function marks(runs: Runs, n: number): Modifies<{ values: "any"; "runs.open[*]": "any" }, number[]> {
  const out: number[] = [];
  for (let i = 0; i < n; i++) out.push(i);
  runs.open.push(n);
  return out;
}
