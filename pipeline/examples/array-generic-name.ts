// `Array<T>` and `ReadonlyArray<T>` are the array types `T[]` and
// `readonly T[]`, spelled by name: one array type, so values pass between
// the spellings, and the prototype's methods apply to both.
function sum(xs: Array<number>): number {
  return xs.reduce((a: number, x: number): number => a + x, 0);
}

function view(xs: number[]): ReadonlyArray<number> {
  return xs;
}

function back(xs: Array<string>): string[] {
  return xs;
}

function pushed(xs: Array<Array<number>>, n: number): number {
  return xs.push([n]);
}

type Pair = Array<boolean> | ReadonlyArray<string>;

function firstOf(p: ReadonlyArray<Pair>): Pair | undefined {
  return p.at(0);
}

function total(): number {
  const xs: Array<number> = [1, 2, 3];
  return sum(xs) + sum(back(["a"]).map((s: string): number => 1));
}
