// Rule mapped-keyof-string refuses a key that reads as a number: TypeScript
// accepts this program, keeping `a` and dropping the number key `0`.
type KS<X> = { [K in keyof X & string]: X[K] };

export function make(): KS<{ 0: string; a: number }> {
  return { a: 1 };
}
