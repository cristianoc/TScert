// Rule mapped-keyof-string: `keyof X & string` drops the number key `0`, so
// TypeScript rejects a value with a field `0`. The front end holds `0` and
// `"0"` alike and refuses the key.
type KS<X> = { [K in keyof X & string]: X[K] };

export function extraNumericKey(): KS<{ 0: string; a: number }> {
  // @ts-expect-error '0' does not exist in type
  return { a: 1, 0: "x" };
}
