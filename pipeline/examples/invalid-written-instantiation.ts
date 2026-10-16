// A `typeof` instantiating a value's generic signature: its binders' bounds
// are checked only at a call, so the instantiation is refused.
function id<T extends string>(x: T): T {
  return x;
}
export function f(x: keyof { a: typeof id<number> }): "a" {
  return x;
}
