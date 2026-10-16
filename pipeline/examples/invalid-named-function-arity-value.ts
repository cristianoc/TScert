// A function value known only by its type may read positions its type does
// not mention: `g` meets `(x: number) => string`, and `map` passes it an
// index, so `mapArr([1], g)` holds the number 0. Only a module function's own
// code is known to discard further actuals.
function mapArr<T, U>(arr: Array<T>, f: (x: T) => U): Array<U> {
  return arr.map(f);
}
function g(x: number, y?: string): string {
  return y ?? String(x);
}
export function main(): string[] {
  return mapArr([1], g);
}
