// The `length` of a union of arrays, of different element types, presence,
// writability and length, compared in branch tests and returned: each member
// is one array contract, whose `length` is its store's, a number, read where
// the test runs, after a write that grows or shrinks the array.
export function longer(
  xs: readonly number[] | string[],
  ys: readonly (boolean | undefined)[],
): boolean {
  if (xs.length !== ys.length) return xs.length > ys.length;
  return false;
}

export function grown(flag: boolean, more: number[]): boolean {
  const xs = flag ? [1, 2] : ["a"];
  more.push(3);
  const ys = flag ? more : [];
  if (!(xs.length === ys.length)) return true;
  return false;
}

export function shrunk(
  flag: boolean,
  more: number[],
  other: readonly string[],
): boolean {
  const xs = flag ? more : other;
  const alias = xs;
  more.pop();
  if (alias.length !== xs.length) return true;
  return false;
}

export function tuples(
  x: readonly [number] | readonly [number, number],
): boolean {
  if (x.length !== 2) return true;
  return false;
}
