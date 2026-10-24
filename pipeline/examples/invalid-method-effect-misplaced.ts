// `Within` at a parameter's type: it states a written signature's effect at
// its result annotation only.
export function f(x: Within<{ value: "keep"; store: "keep" }, number>): number {
  return x;
}
