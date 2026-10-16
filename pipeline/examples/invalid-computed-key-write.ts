// The key added may be `b`: the object is no `{ a: number }`.
export function oneOf(key: "a" | "b"): { a: number } {
  const obj = {};
  obj[key] = 42;
  return obj;
}
