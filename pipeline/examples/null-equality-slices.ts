// A value found equal to `null` or `undefined` is that value, and one found
// unequal to `null` any other kind: of `unknown`, by its kinds; of a named
// union, by its definition's arms. A decoder's optional string field: null,
// or a string, the other answer of `reason !== null`.
// Census: unchecked.mts#decodeResult.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };

export function nullOrString(reason: unknown): string | null {
  if (reason !== null && typeof reason !== "string") return null;
  return reason;
}

export function absent(value: unknown): undefined | number {
  if (value === undefined) return value;
  return 0;
}

export function decoded(
  file: Json | undefined,
  reason: Json | undefined,
): { file: string; reason: string | null } | null {
  if (
    typeof file !== "string" ||
    (reason !== null && typeof reason !== "string")
  )
    return null;
  return { file, reason };
}

export function missing(value: Json | undefined): null | undefined | number {
  if (value == null) return value;
  return 0;
}
