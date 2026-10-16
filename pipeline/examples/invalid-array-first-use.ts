// The first use commits the literal to `number[]`, which is no pair.
declare function takesArray(values: number[]): void;
export function bad(): [number, number] {
  const values = [1, 2];
  takesArray(values);
  const pair: [number, number] = values;
  return pair;
}
