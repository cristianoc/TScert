// A recursive dictionary of JSON values meets `JSON.stringify`'s parameter
// at every depth, and the call keeps `map`'s result dense.
type Json = null | boolean | number | string | { readonly [key: string]: Json };
export function serialized(values: Json[]): string[] {
  return values.map((v: Json) => JSON.stringify(v));
}
