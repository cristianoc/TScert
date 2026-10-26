// Mapped types whose value is `X[P]` at a named type X, an alias or an
// interface: X's outer record shape at the reference's arguments, its
// fields keeping the types they are declared at and its index its readonly
// flag (rule mapped-identity).
type Source = { readonly a: number; b?: string };
interface Shape {
  readonly a: number;
  b?: string;
  c: boolean;
}
type Copy = { [P in keyof Shape]: Shape[P] };
interface Table {
  [key: string]: number;
}

export function read(p: Readonly<Source>): number {
  return p.a;
}
export function partial(p: Partial<Shape>): number {
  return (p.a ?? 0) + (p.c === true ? 1 : 0);
}
export function required(p: Required<Shape>): string {
  return p.b;
}
export function picked(p: Pick<Shape, "a" | "c">): boolean {
  return p.c;
}
export function copied(c: Copy): number {
  return c.a + (c.b ?? "").length;
}
export function made(): Partial<Shape> {
  return { c: true };
}
export function viewed(s: Shape): Readonly<Shape> {
  return s;
}
export function entry(t: Readonly<Table>): number | undefined {
  return t["a"];
}
