// Ordinary read equality permits undefined at a missing or undefined field.
type Expression =
  | { kind: "property"; name: { text: string } }
  | { kind: "other" };
export function wrong(node: { expression?: Expression }): Expression {
  if (node.expression?.kind === "property") return { kind: "other" };
  if (node.expression?.kind === "other") return { kind: "other" };
  return node.expression;
}
