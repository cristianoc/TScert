// The inferred Object.assign target type is a mapped identity written over a
// named record, settled before use.
interface Item {
  readonly value: number;
}
export function read(item: Item): number {
  const f = Object.assign(
    (value: { readonly [P in keyof Item]: Item[P] }): number => value.value,
    { offset: 1 },
  );
  return f(item) + f.offset;
}
