// `typeof x === "object"` also holds for null: the arm keeps it.
export function notNull(x: { a: number } | null): { a: number } {
  if (typeof x === "object") {
    return x;
  }
  return { a: 0 };
}
