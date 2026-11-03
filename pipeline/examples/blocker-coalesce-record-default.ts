// A record literal on the right of `??` is built at the left operand's type,
// at the arm of a discriminated union its literal-valued fields select, and
// the pair holding it is built at a map's tuple value type.
// Census functions:
// fragment-expressions.mts#lambda.
type P = { k: "name"; name: string } | { k: "obj"; fields: P[] };
export function a(ps: (P | undefined)[], d: string | null): Map<string, [P, string | null]> {
  const bound = new Map<string, [P, string | null]>();
  const target = ps[0] ?? { k: "name", name: "x" };
  bound.set("h", [target, d]);
  return bound;
}
export function b(target: P, d: string | null): Map<string, [P, string | null]> {
  const bound = new Map<string, [P, string | null]>();
  bound.set("h", [target, d]);
  return bound;
}
