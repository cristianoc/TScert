// The first use expecting a type, after a `length` read, commits the
// `flatMap` result to `number[]`, which is no pair.
declare function takesArray(values: number[]): void;
export function bad(items: readonly number[]): [number, number] {
  const values = items.flatMap((n) => [n]);
  const count = values.length;
  takesArray(values);
  const pair: [number, number] = values;
  return count > 1 ? pair : [0, 0];
}
