// Mapped types whose value is `X[P]` at a record X: `Readonly`, `Partial`,
// `Required` and `Pick` from the library, and one written over `keyof`.
// `Required` makes an optional field required.
type Copy = {
  [P in keyof { readonly a: number; b?: string }]: {
    readonly a: number;
    b?: string;
  }[P];
};

export function readOnlyField(p: Readonly<{ a: number; b: string }>): number {
  return p.a;
}
export function picked(p: Pick<{ a: number; b: string }, "a">): number {
  return p.a;
}
export function required(p: Required<{ a: number; b?: string }>): string {
  return p.b;
}
export function partial(p: Partial<{ a: number }>): number {
  return p.a ?? 0;
}
export function copied(c: Copy): number {
  return c.a + (c.b ?? "").length;
}
export function widened(s: { a: number }): Readonly<{ a: number }> {
  return s;
}
export function indexed(
  p: Readonly<{ [k: number]: string }>,
): string | undefined {
  return p[0];
}
export function pickedNumeric(p: Pick<{ 0: number; b: string }, 0>): number {
  return p[0];
}
