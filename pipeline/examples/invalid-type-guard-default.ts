// `isStr` tests its parameter, which a missing argument leaves at its
// default: `f(undefined)` returns `undefined` at `string`. The promise is
// about the argument, which at the return may be `undefined`.
export function isStr(x: unknown = "a"): x is string {
  return typeof x === "string";
}

export function f(v: unknown): string {
  return isStr(v) ? v : "";
}
