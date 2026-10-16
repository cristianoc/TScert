// An application whose argument is a string pattern, outside the fragment:
// its obligation cannot be stated.
type B<T extends string> = T;
export function f(x: keyof { a: B<`a${string}`> }): "a" {
  return x;
}
