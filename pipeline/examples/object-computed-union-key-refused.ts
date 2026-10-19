// A computed key at a union of literals: the allocation's key is known only
// at run time, so the literal is refused.
export function pick(k: "a" | "b"): { a?: number; b?: number } {
  return { [k]: 1 };
}
