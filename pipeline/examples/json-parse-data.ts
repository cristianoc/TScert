// `JSON.parse` without a reviver returns plain data: null, a Boolean, a
// number, a string, a hole-free array of such values or an object of them.
// A decoder typed at that data reads arrays densely and dictionaries by key.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export function parse(text: string): Json {
  return JSON.parse(text);
}
export function numbers(text: string): number[] {
  const v: Json = JSON.parse(text);
  if (!Array.isArray(v)) return [];
  return v.map((x: Json) => (typeof x === "number" ? x : 0));
}
export function count(v: Json): number {
  if (v === null || typeof v !== "object") return 0;
  if (Array.isArray(v)) return v.length;
  return Object.keys(v).length;
}
