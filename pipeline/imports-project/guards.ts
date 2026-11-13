// Two guards: `isName` keeps its promise, so its module publishes its entry;
// `isText` returns `true` for a number, so its own unit is refused at that
// return and its module publishes no entry for it.
export function isName(x: string | number): x is string {
  return typeof x === "string";
}

export function isText(x: string | number): x is string {
  return typeof x === "number" || x.length > 0;
}
