// An array literal's store takes fresh locations past the heap's end: what a
// guard found of a field before it is still known after it. An element of an
// `as const` literal that is no literal keeps its own type, as TypeScript's
// const context does.
export function kept(x: { f: 1 | 2 }): 1 {
  if (x.f === 1) {
    const xs = [x.f, 3];
    const pair = [x, x.f] as const;
    const one: 1 = x.f;
    return one;
  }
  return 1;
}
// An array pattern reads its positions from a store, after which nothing
// is known of the heap: the fact the element was read with is its binding's.
export function snapshot(x: { f: 1 | 2 }): 1 {
  if (x.f === 1) {
    const [first] = [x.f] as const;
    x.f = 2;
    return first;
  }
  return 1;
}
// An array's length reads its store, a field read, then counts it, reading
// no heap: what a guard found is still known after it.
export function counted(x: { f: 1 | 2 }, xs: number[]): 1 {
  if (x.f === 1) {
    const n = xs.length;
    const one: 1 = x.f;
    return n > 0 ? one : 1;
  }
  return 1;
}
