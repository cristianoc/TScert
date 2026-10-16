// A callback returning a value that is no array, at `U`: `flatMap` flattens
// it where it is one, so at `U := number[]` the result holds numbers typed
// `number[]`. `first()` returns the number 1 at `number[]`.
export function each<U>(xs: number[], g: (x: number) => U): U[] {
  return xs.flatMap((x: number): U => g(x));
}

export function first(): number[] {
  const row = each([1], (x: number): number[] => [x])[0];
  return row === undefined ? [] : row;
}
