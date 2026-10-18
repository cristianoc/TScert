// A contextual closure parameter at a named generic declaration's instance
// is that reference at its arguments, and the declaration is read as
// written with each binder at its argument: an optional member keeps its
// written contract, distinct at `number`, `number | undefined` and `never`
// (absent only).
interface Box<T> {
  v?: T;
}

export function numbers(bs: readonly Box<number>[]): (number | undefined)[] {
  return bs.map((b) => b.v);
}

export function undefinedAdmitted(
  bs: readonly Box<number | undefined>[],
): (number | undefined)[] {
  return bs.map((b) => b.v);
}

export function absent(bs: readonly Box<never>[]): undefined[] {
  return bs.map((b) => b.v);
}

// The instance reached through a binding of the array.
interface Holder {
  readonly boxes: readonly Box<string>[];
}

export function aliased(h: Holder): (string | undefined)[] {
  const xs = h.boxes;
  return xs.map((b) => b.v);
}
