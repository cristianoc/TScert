// Census functions: fragment-expressions.mts#expr,#objectFields,#optionalChain,
// #optionalMethodCall,#wrappedMethodCall,#chainLink,#update,#template,#binary,#lambda.
// Repeating a tested member path after an earlier conditional keeps its read link.
type Expression =
  | { kind: "property"; name: { text: string } }
  | { kind: "other" };
export function reuse(node: { expression: Expression }): number {
  if (
    node.expression.kind === "property" &&
    node.expression.name.text === "apply"
  )
    return 0;
  if (
    node.expression.kind === "property" &&
    ["call", "bind"].includes(node.expression.name.text)
  )
    return 1;
  return 0;
}

export function optionalReuse(node: { expression?: Expression }): number {
  if (!node.expression) return 0;
  if (
    node.expression.kind === "property" &&
    node.expression.name.text === "apply"
  )
    return 0;
  if (
    node.expression.kind === "property" &&
    ["call", "bind"].includes(node.expression.name.text)
  )
    return 1;
  return 0;
}

export function kept(
  node: { expression: Expression },
  keep: () => Modifies<{}, void>,
): number {
  if (
    node.expression.kind === "property" &&
    node.expression.name.text === "apply"
  )
    return 0;
  if (
    node.expression.kind === "property" &&
    ["call", "bind"].includes(node.expression.name.text) &&
    (keep(), true)
  )
    return 1;
  return 0;
}
