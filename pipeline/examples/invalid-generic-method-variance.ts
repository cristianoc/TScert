// TypeScript relates a method's parameters bivariantly, so it lets a
// `Sink<number>` be a `Sink<number | string>`; through that view `send` would
// hand the sink a string. A quantified member's parameters are contravariant:
// refused.
interface Sink<T> {
  send<U>(value: T, tag: U): U;
}
export function widen(s: Sink<number>): Sink<number | string> {
  return s;
}
