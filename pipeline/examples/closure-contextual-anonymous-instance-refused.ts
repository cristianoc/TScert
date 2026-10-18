// A contextual closure parameter at an anonymous record of a generic
// declaration, at an instance (`{ v?: T }` at `Opt<number>`), reached
// through a binding: the compiler's API gives the instance's members but
// not the instantiation of `T`, and `v`'s type carries the `undefined`
// optionality adds, so `v?: number` is not told from `v?: number | undefined`.
interface Opt<T> {
  readonly items: readonly { v?: T }[];
}

export function aliased(o: Opt<number>): (number | undefined)[] {
  const xs = o.items;
  return xs.map((i) => i.v);
}
