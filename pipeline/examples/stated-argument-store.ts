// Frames stating a parameter's store region (docs/drafts/stated-effects.md,
// §4): `shrink` pops and splices the array it is handed and `trim` pops its
// second parameter's, each changing value locations and that store alone, so
// each states `values: "any"` and the parameter's region `"xs[*]": "any"`,
// every other store kept. A `this` parameter names the receiver's store.
export function shrink(xs: number[]): Modifies<{ values: "any"; "xs[*]": "any" }, void> {
  xs.pop();
  xs.splice(0, 1);
}

export function trim(n: number, xs: number[]): Modifies<{ values: "any"; "xs[*]": "any" }, number> {
  xs.pop();
  return n;
}

export function clear(this: number[]): Modifies<{ values: "any"; "this[*]": "any" }, void> {
  this.splice(0);
}
