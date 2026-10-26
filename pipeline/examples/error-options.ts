// `Error`'s options, read for `cause`: absent, `undefined`, or an object
// whose type states `cause`, at which `HasProperty` and `Get` run no code.
// The error's own `cause` is not stated. A class extending `Error` passes
// them through `super`, also through its implicit constructor.
class Caused extends Error {
  constructor(m: string, cause: unknown) {
    super(m, { cause });
  }
}
class Plain extends Error {}
class Deeper extends Caused {}
export function make(
  m: string,
  cause: unknown,
  options: { cause: unknown },
  none: undefined,
): string[] {
  return [
    new Error(m, { cause }).message,
    Error(m, { cause: 1 }).message,
    new Error(m, cause === undefined ? undefined : { cause }).message,
    new Error(m, {}).message,
    new Error(m, none).message,
    new Error(m, options).message,
    new Caused(m, cause).message,
    new Plain(m, { cause }).message,
    new Deeper(m, cause).message,
  ];
}
// Within the empty footprint: a callback calling it keeps `map`'s result
// dense.
export function dense(xs: string[]): string[] {
  return xs.map((x) => Error(x, { cause: x }).message);
}
