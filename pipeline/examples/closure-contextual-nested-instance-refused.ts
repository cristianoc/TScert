// A contextual closure parameter at an anonymous record of a generic
// declaration whose instance's argument is another instance of the same
// record (`{ v?: T }` at `T` the record `{ v?: string }`): refused where the
// outer record's optional member is read, its instantiation not given by the
// compiler's API.
interface Opt<T> {
  readonly items: readonly { v?: T }[];
}

declare function wrap<T>(items: readonly T[]): Opt<T>;

export function nested(o: Opt<string>): void {
  wrap(o.items).items.forEach((i) => i.v);
}
