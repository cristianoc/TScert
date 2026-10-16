// `never` decided by a naked check type distributes over no member and is
// `never`; wrapped, `[T] extends [U]`, it is decided once, and `[never]`
// extends `[string]`: `Wrapped<never>` is `"yes"`, no value of `"no"`.
type Naked<T> = T extends string ? "yes" : "no";
type Wrapped<T> = [T] extends [string] ? "yes" : "no";
function naked(x: Naked<never>): "no" {
  return x;
}
export function wrapped(x: Wrapped<never>): "no" {
  return naked(x);
}
