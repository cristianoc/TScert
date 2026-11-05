// An object substitution of `String.raw`, whose ToString runs its
// `toString`: TypeScript admits any substitution, and this one writes the
// narrowed `x` before the function returns it as a number. Under Node,
// `shown()` is the string "b". Refused: a string concatenates only with a
// primitive.
export function shown(): number {
  let x: number | string = 1;
  const text: string = String.raw`a${{
    toString(): string {
      x = "b";
      return "";
    },
  }}`;
  return text.length > 0 ? x : 0;
}
