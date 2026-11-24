// A function literal at a key of a literal where a dictionary is expected
// takes the index's value contract, without the `undefined` an absent read
// adds: `() => []` is walked at `() => P[]`, its `[]` made at `P[]`.
// Census functions:
// intrinsics.mts#intrinsics.
type P = { name: string };
export function f(): number {
  const definitions: Record<string, () => P[]> = {
    a: () => [],
  };
  return Object.keys(definitions).length;
}
