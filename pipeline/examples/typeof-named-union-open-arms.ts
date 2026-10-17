// A `typeof` test of a named union with a type parameter or an
// intersection among its arms: the arms the test cannot decide stay, so the
// failed test leaves the parameter's and the intersection's values.
type Either<T> = string | T;
export function nonString<T extends { size: number }>(k: Either<T>): number {
  return typeof k === "string" ? -1 : k.size;
}
type Joined = string | ({ a: number } & { b: number });
export const joined = (k: Joined): number =>
  typeof k === "string" ? -1 : k.a + k.b;
