// An explicit receiver test before a conditional record allocation.
// The call preserves the store, as Gate.span does at the census sites.
// Census functions:
// fragment-classes.mts#classStmt
// fragment-classes.mts#classBody
type Expr = { k: "id"; pos: number; name: string };
export function base(
  base: { proto: string | null } | null,
  present: { expression: string } | undefined,
  span: (expression: string) => Modifies<{}, number>,
): Expr | null {
  const value: Expr | null =
    base && base.proto && present
      ? { k: "id", pos: span(present.expression), name: base.proto }
      : null;
  return value;
}
