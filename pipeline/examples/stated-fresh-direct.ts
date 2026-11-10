// The regional check as a second certificate of a claimed footprint
// (FOOTPRINTS.md, "Fresh array storage"): `f` states no store region, and
// the call of `step` changes the store of `open`, an array `f` allocates.
// The plain bound check reads a frame stating a region as changing every
// store; the regional check with no regions rebases the region on `open`,
// whose store lies at or above the entry heap's length, to no region, so
// `f` changes the stores of its entry heap at most by `grow`.
function step(open: number[], out: number[]): Modifies<{ values: "any"; stores: "grow"; "open[*]": "any" }, number> {
  open.pop();
  out.push(1);
  return out.length;
}

export function f(xs: number[]): Modifies<{ values: "any"; stores: "grow" }, number> {
  const open: number[] = [1];
  return step(open, xs);
}
