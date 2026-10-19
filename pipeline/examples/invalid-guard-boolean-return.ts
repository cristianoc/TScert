// A guard's Boolean return answers `true` of `null` too: where it returns
// `true` the actual may be `null`, which the promise does not admit.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export function isText(v: Json): v is string {
  return typeof v === "string" || v === null;
}
