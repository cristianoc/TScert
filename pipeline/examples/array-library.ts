// More of Array.prototype through the prototype: readers on any array, and
// mutators on a mutable one, each at the types TypeScript declares.
function held(xs: readonly boolean[]): boolean[] {
  return xs.filter((x: boolean): boolean => x);
}

function allHeld(xs: readonly boolean[]): boolean {
  return xs.every((x: boolean): boolean => x);
}

function describe(xs: readonly string[]): string {
  return xs.slice(1).join(", ");
}

function has(xs: readonly number[], n: number): boolean {
  return xs.includes(n);
}

function first(xs: readonly number[]): number | undefined {
  return xs.at(0);
}

function grow(xs: number[], n: number): number | undefined {
  xs.push(n, n);
  return xs.pop();
}

function firstHeld(xs: readonly boolean[]): boolean | undefined {
  return xs.find((x: boolean): boolean => x);
}
