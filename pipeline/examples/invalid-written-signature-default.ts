// A parameter initializer in a signature inside a type is erased: the call
// never runs, and is refused.
declare function key<T extends string>(): number;
export function f(
  x:
    | keyof { m(x?: number): void; a: number }
    | keyof { n(y: number = key<any>()): void },
): "m" | "a" | "n" {
  return x;
}
