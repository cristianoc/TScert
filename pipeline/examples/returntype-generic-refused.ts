// ReturnType of a generic function's typeof: TypeScript instantiates its
// type parameter at its bound, a value type the reader does not state.
function first<T>(xs: T[]): T | undefined {
  return xs[0];
}
export function head(xs: number[]): number {
  type Head = ReturnType<typeof first>;
  const found: Head = first(xs);
  return typeof found === "number" ? found : 0;
}
