// `Readonly` at a named type makes each of its fields readonly: a write
// through an assertion to a writable record is refused.
interface Shape {
  a: number;
}
export function write(p: Readonly<Shape>): void {
  (p as { a: number }).a = 1;
}
