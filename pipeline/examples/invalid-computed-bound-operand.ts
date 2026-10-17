// An application inside a computed type keeps its bound, though TypeScript
// computes `"a"` for `keyof Box<number>` without it.
interface Box<T extends string> {
  a: T;
}
export function f(x: keyof Box<number>): "a" {
  return x;
}
