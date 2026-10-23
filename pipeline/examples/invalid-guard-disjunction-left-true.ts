// The left disjunct's true answer reaches the result without the right
// one's test: a `{ k: "a" }` without `a` answers `true`. Run under Node.
type U = { k: "a"; a?: string } | { k: "b"; b: string };

export function right(p: U): p is { k: "b"; b: string } {
  return p.k === "a" && !p.a || p.k === "b";
}
