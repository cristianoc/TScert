// Generic map result inference needs to retain a literal in a callback result
// union before a later every call.
// Census functions:
// fragment-expressions.mts#binary, fragment-expressions.mts#chainLink,
// fragment-expressions.mts#expr, fragment-expressions.mts#knownLocal,
// fragment-expressions.mts#lambda, fragment-expressions.mts#localArrow,
// fragment-expressions.mts#memberOf, fragment-expressions.mts#objectFields,
// fragment-expressions.mts#optionalChain, fragment-expressions.mts#template,
// fragment-expressions.mts#update.
export function use(
  values: number[],
  read: (
    n: number,
  ) => Within<{ value: "keep"; store: "keep" }, boolean | "absent">,
): boolean {
  const parts = values.map((n) => read(n));
  return parts.every((x) => x === "absent");
}
