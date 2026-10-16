// `isString` answers `true` for numbers, which TypeScript does not check:
// `shout(1)` calls `toUpperCase` on a number. Its promise unit returns the
// argument where it answers `true`, a number, at `string`.
export function isString(x: unknown): x is string {
  return typeof x === "number";
}

export function shout(v: unknown): string {
  return isString(v) ? v.toUpperCase() : "";
}
