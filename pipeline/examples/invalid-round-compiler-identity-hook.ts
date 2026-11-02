// An extra callable key cannot enter a compiler identity's JSON data bound.
type Json = null | boolean | number | string | readonly Json[] | JsonObject;
type JsonObject = { readonly [key: string]: Json };
type Result = ({ unobserved: string } | { identity: string }) & JsonObject;
function identify(): Result {
  return { unobserved: "missing compiler", toJSON: (): undefined => undefined };
}
export function current(): string {
  return JSON.stringify(identify());
}
