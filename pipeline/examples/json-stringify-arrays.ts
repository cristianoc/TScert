// Arrays of JSON values, nested at any depth, meet `JSON.stringify`'s
// parameter: an array owns no `toJSON` and inherits none, so the call runs
// no hook, returns a string and keeps `map`'s result dense.
type Json =
  | null
  | boolean
  | number
  | string
  | readonly Json[]
  | { readonly [key: string]: Json };
export function nested(rows: readonly (readonly number[])[]): string {
  return JSON.stringify(rows);
}
export function mixed(values: Json[]): string[] {
  return values.map((v: Json) => JSON.stringify([v, [v, null]]));
}
