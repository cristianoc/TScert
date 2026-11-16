// The regional check as a second certificate of a claimed footprint
// (FOOTPRINTS.md, "Fresh array storage"): `f` states no spine region, and
// the call of `step` changes the spine of `open`, an array `f` allocates.
// The plain bound check reads a frame stating a region as changing every
// spine; the regional check with no regions rebases the region on `open`,
// whose spine lies at or above the entry heap's length, to no region, so
// `f` changes the spines of its entry heap at most by `grow`.
function step(open: number[], out: number[]): Modifies<{ values: "any"; spines: "grow"; "open[*]": "any" }, number> {
  open.pop();
  out.push(1);
  return out.length;
}

export function f(xs: number[]): Modifies<{ values: "any"; spines: "grow" }, number> {
  const open: number[] = [1];
  return step(open, xs);
}
