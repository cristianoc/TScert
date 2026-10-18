// A contextual closure parameter at a generic declaration's record whose
// optional member is at a binder: TypeScript gives the member at its
// instance, with the `undefined` optionality adds, and the written optional
// contract at `number | undefined` is not recovered from it.
interface Opt<T> {
  readonly items: readonly { v?: T }[];
}

export function values(o: Opt<number | undefined>): (number | undefined)[] {
  return o.items.map((i) => i.v);
}
