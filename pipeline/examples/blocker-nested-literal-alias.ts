// A record literal expected at a discriminated union selects its arm by a
// literal field whose type is a union naming another alias: the literal is
// admitted through the named alias's members.
// Census functions:
// fragment-expressions.mts#template.
type Span = [start: number, end: number];
type ArithOp = "add" | "sub";
type BinaryOp = ArithOp | "lt";
type E =
  | { k: "lit"; pos: Span; v: string }
  | { k: "arith"; pos: Span; op: BinaryOp; l: E; r: E };
export function a(l: E, r: E): E {
  const value: E = { k: "arith", pos: [0, 1], op: "add", l, r };
  return value;
}
