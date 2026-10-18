// A contextual closure parameter at a generic declaration's record read
// at the instance its callee reads it from: the written record with each
// binder at that instance's argument, so an optional member keeps its
// written contract, distinct at `number`, `number | undefined` and `never`
// (absent only).
interface Opt<T> {
  readonly items: readonly { v?: T }[];
}

export function numbers(o: Opt<number>): (number | undefined)[] {
  return o.items.map((i) => i.v);
}

export function undefinedAdmitted(
  o: Opt<number | undefined>,
): (number | undefined)[] {
  return o.items.map((i) => i.v);
}

export function absent(o: Opt<never>): undefined[] {
  return o.items.map((i) => i.v);
}

// The instance reached through a member read off another record, and
// through an alias naming it.
interface Outer {
  readonly inner: Opt<string>;
}
type Strings = Opt<string>;

export function nested(o: Outer, s: Strings): (string | undefined)[] {
  o.inner.items.forEach((i) => i.v);
  return s.items.map((i) => i.v);
}

// The record the forged control (`pipeline/test.mts`) claims `absent`'s
// closure at: `v` optional at `undefined`.
export function forgedAt(present: { v?: undefined }): boolean {
  return present.v === undefined;
}
