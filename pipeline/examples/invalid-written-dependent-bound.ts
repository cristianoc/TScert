// A binder bounded by another meets only what that one meets:
// `U extends T`, `T extends number` gives no `string`.
type B<T extends string> = T;
export function f<T extends number, U extends T>(x: B<U>): number {
  return 1;
}
