// An interface redeclaring its base's member at a narrower type: the reader
// admits an inherited member only where it is disjoint from the own ones or
// declared alike, and refuses the shape.
interface Base {
  kind: string;
}
interface Narrow extends Base {
  kind: "narrow";
}
export function kind(n: Partial<Narrow>): string {
  return n.kind ?? "";
}
