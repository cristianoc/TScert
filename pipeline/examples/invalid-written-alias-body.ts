// An application in a computed alias's body keeps its bound: `any` is read
// as `unknown`, no `string`.
interface Box<T extends string> {
  a: T;
}
type Key<T> = keyof Box<any>;
export function f(x: Key<number>): "a" {
  return x;
}
