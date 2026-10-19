// `JSON.parse` defines every member as an own data property holding JSON
// data, never a function: a member named "toJSON", at any depth, is one
// `JSON.stringify` reads and does not call, so the text round-trips.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export function roundTrip(text: string): string {
  const parsed: Json = JSON.parse(text);
  return JSON.stringify(parsed);
}
export function wrapped(text: string): string {
  return JSON.stringify([JSON.parse(text), { toJSON: JSON.parse(text) }]);
}
