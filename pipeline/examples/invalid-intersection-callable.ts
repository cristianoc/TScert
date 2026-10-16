// A callable with fields reads its fields at their types: `a` is a number.
export function bad(h: (() => void) & { a: number }): string {
  return h.a;
}
