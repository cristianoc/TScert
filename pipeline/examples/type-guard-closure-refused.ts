// A guard closure inside a function would have a promise unit closing over
// the bindings around it.
export function size(v: unknown): number {
  const isString = (x: unknown): x is string => typeof x === "string";
  return isString(v) ? v.length : 0;
}
