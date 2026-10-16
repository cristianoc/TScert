// `str` completes for every value but a number, which TypeScript does not
// check: `length(true)` reads `length` off a Boolean, `undefined`. Where the
// body completes, its argument is unknown, not within the promise's `string`.
export function str(v: unknown): asserts v is string {
  if (typeof v === "number") throw Error("a number");
}

export function length(v: unknown): number {
  str(v);
  return v.length;
}
