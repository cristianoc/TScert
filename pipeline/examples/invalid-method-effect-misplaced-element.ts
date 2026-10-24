// `Within` at an array's element type: no signature's result.
export function f(
  xs: Within<{ value: "keep"; store: "keep" }, number>[],
): number {
  return xs.length;
}
