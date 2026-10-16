// `isString` answers `true` for `undefined` too, which TypeScript does not
// check: `label(undefined)` returns `undefined` at `string`. Its promise unit
// returns the argument where it answers `true`, `undefined` among them, at
// `string`.
export function isString(x: unknown): x is string {
  return typeof x === "string" || x === undefined;
}

export function label(v: unknown): string {
  return isString(v) ? v : "none";
}
