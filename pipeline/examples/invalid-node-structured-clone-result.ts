// A getter beside a JSON array's elements may change what `structuredClone`
// reads after it: popping the enclosing array leaves a hole in its copy (run
// under Node), which is no JSON value. The result is `unknown`, refused as
// `Json`.
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
