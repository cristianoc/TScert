// A frame excepting one parameter's spine while the body changes another's:
// `drop` states `xs`'s spine region and pops `ys`, whose spine the statement
// keeps, so the region check refuses the pop. Under Node, `drop([1], [2])`
// leaves `ys` empty, where the statement says its spine is unchanged.
export function drop(xs: number[], ys: number[]): Modifies<{ values: "any"; "xs[*]": "any" }, void> {
  ys.pop();
}
