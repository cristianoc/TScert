// A `find` callback calling a recursive constant: the closure's body reads
// its self entry at the footprint proposed for the closure, which the
// closure's check establishes by induction on the step index, so the closure
// changes no storage, the callback is within the empty footprint and each
// visit passes an element at `Tree`. Module-level and local, of one
// parameter and capturing another, recursing through a `some` callback.
type Tree = { readonly leaf: boolean; readonly children: readonly Tree[] };

const closed = (t: Tree): boolean =>
  t.leaf || t.children.some((c) => closed(c));

export function firstClosed(list: readonly Tree[]): Tree | undefined {
  return list.find((t) => closed(t));
}

export function firstDeep(list: readonly Tree[], depth: number): number {
  const deep = (t: Tree, d: number): boolean =>
    d <= 0 || t.children.some((c) => deep(c, d - 1));
  return list.findIndex((t) => deep(t, depth));
}

export function firstAnnotated(list: readonly Tree[]): Tree | undefined {
  const open: (t: Tree) => boolean = (t) =>
    !t.leaf && t.children.every((c) => open(c));
  return list.find((t) => open(t));
}
