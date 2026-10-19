// A guard of one literal over `JsonValue | undefined`. The same guard over
// `unknown`, `JsonValue` or `string | undefined` verifies.
type JsonValue =
  | null
  | boolean
  | number
  | string
  | readonly JsonValue[]
  | { readonly [key: string]: JsonValue };
type JsonRead = JsonValue | undefined;

export function isDense(value: JsonRead): value is "dense" {
  return value === "dense";
}
