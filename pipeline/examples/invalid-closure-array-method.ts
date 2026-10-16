// Inside a closure, an array method's result is its instance's: a number
// reduction is not a string.
export function total(xs: number[]): () => string {
  return (): string => xs.reduce((p: number, c: number): number => p + c, 0);
}
