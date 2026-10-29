// A map callback over a union of array types whose object literal fits no
// arm of the expected element type is refused: its discriminant `"call"` is
// no arm's.
type Span = [number, number];
type Expr =
  | { k: "id"; pos: Span; name: string }
  | { k: "num"; pos: Span; value: number };
type Param = { pos: Span; name: string; at: Span };

export function actuals(written: readonly string[] | null, base: Param[] | null): Expr[] {
  const params = written
    ? written.map((name) => ({ pos: [0, 1] as Span, name }))
    : base ? base : [];
  // @ts-expect-error: "call" is no arm's discriminant.
  let actuals: Expr[] = params.map((p) => ({ k: "call", pos: p.pos, name: p.name }));
  return actuals;
}
