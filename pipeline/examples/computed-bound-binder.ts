// An application naming a binder of a type a computation replaces is
// checked under that binder's bound: `U extends string` meets `B`'s.
type B<T extends string> = T;
export function f(x: keyof { a: <U extends string>() => B<U> }): "a" {
  return x;
}
