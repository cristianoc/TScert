// A parameter whose default is taken holds the type its annotation names: a
// copy of the set by `new Set` reads its element type from it, also inside a
// closure, as `computedAlias` (type-term.mts) copies its `seen` set.
export function copy(seen: Set<number> = new Set()): number {
  return new Set(seen).size;
}

export function copiedInClosure(seen: Set<number> = new Set()): boolean {
  const grown = (n: number): boolean => {
    const next = new Set(seen);
    next.add(n);
    return next.size > seen.size;
  };
  return grown(1);
}

// An alias naming a union with undefined: the default replaces the undefined
// arm, and the binding holds the alias's defined arm.
type MaybeSet = Set<string> | undefined;
export function aliased(names: MaybeSet = new Set()): number {
  return new Set(names).size;
}
