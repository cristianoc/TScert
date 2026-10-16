// `str` completes for every value but a number, which TypeScript does not
// check: `length(true)` reads `length` off a Boolean, `undefined`. Its
// promise unit returns the argument where it completes, an unknown, at
// `string`.
export function str(v: unknown): asserts v is string {
  if (typeof v === "number") throw Error("a number");
}

export function length(v: unknown): number {
  str(v);
  return v.length;
}
