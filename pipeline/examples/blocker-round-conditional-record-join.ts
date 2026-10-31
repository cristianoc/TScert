// A conditional record allocation rereading a nullable field after a call.
// Census functions:
// fragment-classes.mts#classStmt
// fragment-classes.mts#classBody
type Expr = { k: "id"; pos: number; name: string };
export function base(
  base: { proto: string | null } | null,
  present: { expression: string } | undefined,
  span: (expression: string) => number,
): Expr | null {
  const value: Expr | null =
    base?.proto && present
      ? { k: "id", pos: span(present.expression), name: base.proto }
      : null;
  return value;
}
