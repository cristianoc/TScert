// Array.prototype's members read through each array's prototype: `map` at a
// new element type, `forEach` for its effect, and `sort`, a mutator, on a
// mutable array, which it returns.
function lengths(xs: string[]): number[] {
  return xs.map((x: string): number => 1);
}

function visit(xs: readonly number[]): void {
  xs.forEach((x: number): undefined => undefined);
}

function ascending(xs: number[]): number[] {
  return xs.sort((a: number, b: number): number => a - b);
}
