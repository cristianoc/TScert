// A guard returning a Boolean by its form returns its truth: the return is
// a condition, `true` where it holds and `false` where it fails, and the
// promise is checked where it returns `true`, in the context the test's
// answer leaves. A function body's `return`, an arrow's expression body, a
// disjunction of singleton tests, and a guard's narrowing at its call.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
type Fields = { [key: string]: Json };
export function isFields(v: Json): v is Fields {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}
export function isList(v: Json): v is Json[] {
  return Array.isArray(v);
}
export const isCount = (v: Json): v is number =>
  typeof v === "number" && v >= 0;
export function isMode(v: string): v is "read" | "write" {
  return v === "read" || v === "write";
}
export function size(v: Json): number {
  return isFields(v)
    ? Object.keys(v).length
    : isList(v)
      ? v.length
      : isCount(v)
        ? v
        : 0;
}
