// A binder bounded by a union is below the union, not below one member:
// `T extends string | number` may be a number.
function asString<T extends string | number>(x: T): string {
  return x;
}
