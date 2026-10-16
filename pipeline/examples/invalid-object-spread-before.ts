// A field written before a spread may be overwritten by it: an open record
// may own any key, at any type. TypeScript keeps the field's type.
function fieldBefore(obj: { b: number }): { a: string } {
  return { a: "", ...obj };
}
export function main(): string {
  return fieldBefore({ b: 1 }).a;
}
