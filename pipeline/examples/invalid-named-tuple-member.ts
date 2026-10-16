// A named member keeps its element type: a mutable `end` holds a number, and
// a view widening it to `number | string` would let a write store a string
// there. TypeScript accepts it: its tuples are covariant.
type Span = [start: number, end: number];
export function widen(span: Span): [start: number, end: number | string] {
  return span;
}
export function corrupt(span: Span): number {
  widen(span)[1] = "end";
  return span[1];
}
