// Census: array-prototype.mts#reviewedEntries includes atEachFootprint.
type Signature = { params: number[]; result: number };
const collect = (
  values: readonly number[],
  signature: (n: number) => Modifies<{}, Signature>,
): (Signature & { effect: number })[] =>
  values.map((n) => ({ ...signature(n), effect: n }));
export function broken(values: number[]): (Signature & { effect: number })[] {
  return collect(values, (n) => {
    values.pop();
    return { params: [n], result: n };
  });
}
