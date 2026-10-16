// `Extract<Shape, { k: "a" }>` keeps only the member tagged "a": a member
// tagged "b" is no value of it.
type Shape = { k: "a"; x: number } | { k: "b"; y: string };
export function wrong(
  s: Extract<Shape, { k: "b" }>,
): Extract<Shape, { k: "a" }> {
  return s;
}
