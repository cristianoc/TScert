// Census: array-prototype.mts#reviewedEntries includes atEachFootprint.
type Signature = { params: number[]; result: number };
const collect = (
  values: readonly number[],
  signature: (n: number) => Signature,
): (Signature & { effect: number })[] =>
  values.map((n) => ({ ...signature(n), effect: n }));
export function reviewed(
  values: readonly number[],
): (Signature & { effect: number })[] {
  return collect(values, (n) => ({ params: [n], result: n }));
}
