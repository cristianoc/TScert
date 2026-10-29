// Omit of a union is Pick at the union, whose record the reader does not
// hold: refused.
type Shape = { k: "a"; a: number; n: string } | { k: "b"; b: string; n: string };
export function n(s: Omit<Shape, "k">): string {
  return s.n;
}
