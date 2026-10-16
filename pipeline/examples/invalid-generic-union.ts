// A union mentioning a binder is not below the binder: `string | T` holds a
// string, which `T` need not.
function narrowed<T>(x: string | T): T {
  return x;
}
