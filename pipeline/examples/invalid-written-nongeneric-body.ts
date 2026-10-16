// A non-generic alias's body is swept where it is named.
interface Box<T extends string> {
  a: T;
}
type Key = keyof Box<any>;
export function f(x: Key): "a" {
  return x;
}
