// A diagnostic run of a verified source reports no refusal. The producer types
// each spread operand speculatively, outside the operand's execution, where
// an optional chain's saved receiver is unbound; that query's failure is its
// caller's to answer. It stands for the census's "unbound name ?." sites:
// declaration-graph.mts#selectGlobal and #collect, fragment-classes.mts#classBody
// and #classStmt, fragment-expressions.mts#expr.
type Node = { typeArguments?: readonly string[]; base?: { error?: boolean } };

export function typeArgs(node: Node): { k: string; typeArgs?: string[] } {
  return { k: "new", ...(node.typeArguments?.length ? { typeArgs: node.typeArguments.map((t) => t) } : {}) };
}

export function derived(node: Node): { error?: "derived" } {
  const error: "derived" = "derived";
  return { ...(node.base?.error ? { error } : {}) };
}
