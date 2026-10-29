// A map callback over a receiver whose type is a union of array types
// returning a record, its expected element type fixed by the annotation of the
// `let` it initializes: the callback's parameter is the union of the arms'
// elements, its literal built at the arm it fits.
// Census functions:
// fragment-classes.mts#classBody, fragment-classes.mts#classStmt.
type Span = [number, number];
type Expr =
  | { k: "id"; pos: Span; name: string }
  | { k: "num"; pos: Span; value: number };
type Param = { pos: Span; name: string; at: Span };

export function actuals(written: readonly string[] | null, base: Param[] | null): Expr[] {
  const params = written
    ? written.map((name) => ({ pos: [0, 1] as Span, name }))
    : base ? base : [];
  let actuals: Expr[] = params.map((p) => ({ k: "id", pos: p.pos, name: p.name }));
  return actuals;
}
