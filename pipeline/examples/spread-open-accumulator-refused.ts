// A spread after a spread merges onto the first copy, whose type states no
// field, no own-key bound and no index: it may be a host object, on which a
// merge is stuck (COMPILER-API.md, "Restricted values"). The copy is fresh,
// which its type does not say.
class Counter {
  #count: number = 0;
  next(): number {
    this.#count = this.#count + 1;
    return this.#count;
  }
}

export function spread(c: Counter): { n: number } {
  const copy = { ...c, n: 1 };
  return copy;
}
