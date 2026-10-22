// A recursive guard closure passing its self entry where `every` offers its
// callback more parameters: a guard's self entry is read at its own
// signature, so the read meets no longer one and is refused.
type Term = { readonly k: string; readonly parts: readonly Term[] };
type Leaf = Term & { readonly k: "leaf" };

export function allLeaves(t: Term): boolean {
  const leaf = (u: Term): u is Leaf =>
    u.k === "leaf" && u.parts.every(leaf);
  return leaf(t);
}
