// `Object.getOwnPropertyDescriptor` of a value at a string, number or symbol
// key: `undefined`, or a fresh descriptor whose `value` is `unknown` and whose
// `enumerable` and `configurable` are Booleans. Its operand's type excludes
// host values: a dictionary, a writable array.
export function fieldOf(o: { [k: string]: unknown }, key: string): unknown {
  return Object.getOwnPropertyDescriptor(o, key)?.value;
}

export function rowAt(rows: unknown[], label: number | string): unknown {
  return Object.getOwnPropertyDescriptor(rows, label)?.value;
}

export function visible(o: { [k: string]: unknown }, key: symbol): boolean {
  const descriptor = Object.getOwnPropertyDescriptor(o, key);
  return descriptor !== undefined && descriptor.enumerable;
}
