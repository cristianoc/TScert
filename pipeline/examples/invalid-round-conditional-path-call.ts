// Store growth permits replacing a tested field's value through another alias.
type Expression =
  | { kind: "property"; name: { text: string } }
  | { kind: "other" };
export function wrong(
  node: { expression: Expression | undefined },
  change: () => Within<{ value: "any"; store: "grow" }, void>,
): Expression {
  if (!node.expression) return { kind: "other" };
  if (
    node.expression.kind === "property" &&
    node.expression.name.text === "apply"
  )
    return { kind: "other" };
  if (
    node.expression.kind === "property" &&
    ["call", "bind"].includes(node.expression.name.text) &&
    (change(), true)
  )
    return node.expression;
  return { kind: "other" };
}
