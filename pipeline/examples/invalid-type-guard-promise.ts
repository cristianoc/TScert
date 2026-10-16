// `isString` answers `true` for numbers, which TypeScript does not check:
// `shout(1)` calls `toUpperCase` on a number. Where the body answers `true`,
// its argument is a number, not within the promise's `string`.
export function isString(x: unknown): x is string {
  return typeof x === "number";
}

export function shout(v: unknown): string {
  return isString(v) ? v.toUpperCase() : "";
}
