// Mixed nesting: the outer conjunct tests what the left disjunct already
// answered, and a `{ k: "a" }` without `a` answers `true`. Run under Node.
type U = { k: "a"; a?: string } | { k: "b"; b: string };

export function nested(p: U): p is { k: "a"; a: string } {
  return (p.k === "a" && !p.a || p.k === "b") && p.k === "a";
}
