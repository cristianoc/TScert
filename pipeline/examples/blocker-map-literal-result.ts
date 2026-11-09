// A map whose callback returns a call's declared literal union keeps the
// literal in its element type for a later every call.
// Census functions:
// fragment-expressions.mts#binary, fragment-expressions.mts#chainLink,
// fragment-expressions.mts#expr, fragment-expressions.mts#knownLocal,
// fragment-expressions.mts#lambda, fragment-expressions.mts#localArrow,
// fragment-expressions.mts#memberOf, fragment-expressions.mts#objectFields,
// fragment-expressions.mts#optionalChain, fragment-expressions.mts#template,
// fragment-expressions.mts#update.
export function use(
  values: number[],
  read: (n: number) => Modifies<{}, boolean | "absent">,
): boolean {
  const parts = values.map((n) => read(n));
  return parts.every((x) => x === "absent");
}
