// A merged interface's parameter takes its default and its bound from the
// declaration stating them, though another declaration binds the longer
// list: `I` with no arguments is `I<string, number>`, and `J`'s `T` is
// bounded by `string` where only the shorter declaration says so.
interface I<T = string> {
  a: T;
}
interface I<T, U = number> {
  b: U;
}

interface J<T extends string> {
  key: T;
}
interface J<T, U = boolean> {
  flag: U;
}

export function read(x: I): string {
  return x.a;
}

export function count(x: I): number {
  return x.b;
}

export function key<T extends string>(j: J<T>): string {
  return j.key;
}
