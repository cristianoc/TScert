// `Within` at a guard's promised type: a guard's promise is about its
// argument, and states its footprint beside it already.
export function isNumber(
  x: unknown,
): x is Within<{ value: "keep"; store: "keep" }, number> {
  return typeof x === "number";
}
