// An application naming a binder of a type a computation replaces: its
// obligation holds only under that binder.
type B<T extends string> = T;
export function f(x: keyof { a: <U extends string>() => B<U> }): "a" {
  return x;
}
