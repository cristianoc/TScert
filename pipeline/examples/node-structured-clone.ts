// Node's `structuredClone` of a JSON value, whose members are data: a fresh
// copy, a JSON value, within the empty footprint.
type Json =
  | null
  | boolean
  | number
  | string
  | readonly Json[]
  | { readonly [key: string]: Json };
export function copy(value: Json): Json {
  return structuredClone(value);
}
