// A guard's call answering `true` narrows its actual on the conditional's
// first arm, a closure created there included: the closure reads the actual
// at the promise's type. The other arm reads it at its own type.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
function isRecord(v: Json): v is { [key: string]: Json } {
  if (typeof v !== "object" || v === null || Array.isArray(v)) return false;
  return true;
}
export function present(value: Json): string[] {
  return isRecord(value)
    ? ["kind", "rest"].filter((k) => k in value)
    : ["none"].filter((k) => value === k);
}
