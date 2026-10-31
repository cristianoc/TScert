// A callback may clear the field between its test and the record's read.
type Expr = { k: "id"; pos: number; name: string };
export function base(
  base: { proto: string | null } | null,
  present: { expression: string } | undefined,
  span: (expression: string) => number,
): Expr | null {
  const value: Expr | null =
    base && base.proto && present
      ? { k: "id", pos: span(present.expression), name: base.proto }
      : null;
  return value;
}
