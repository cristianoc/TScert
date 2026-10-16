// `isString` answers `true` for `undefined` too, which TypeScript does not
// check: `label(undefined)` returns `undefined` at `string`. Where the body
// answers `true`, its argument may be `undefined`, not within the promise's
// `string`.
export function isString(x: unknown): x is string {
  return typeof x === "string" || x === undefined;
}

export function label(v: unknown): string {
  return isString(v) ? v : "none";
}
