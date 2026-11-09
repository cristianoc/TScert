// A frame excepting one parameter's store while the body changes another's:
// `drop` states `xs`'s store region and pops `ys`, whose store the statement
// keeps, so the region check refuses the pop. Under Node, `drop([1], [2])`
// leaves `ys` empty, where the statement says its store is unchanged.
export function drop(xs: number[], ys: number[]): Modifies<{ values: "any"; "xs[*]": "any" }, void> {
  ys.pop();
}
