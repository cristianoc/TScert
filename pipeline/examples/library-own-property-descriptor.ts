// `Object.getOwnPropertyDescriptor` of a value at a string, number or symbol
// key: `undefined`, or a fresh descriptor whose `value` is `unknown` and whose
// `enumerable` and `configurable` are Booleans.
export function fieldOf(o: object, key: string): unknown {
  return Object.getOwnPropertyDescriptor(o, key)?.value;
}

export function rowAt(rows: unknown, label: number | string): unknown {
  return Array.isArray(rows)
    ? Object.getOwnPropertyDescriptor(rows, label)?.value
    : undefined;
}

export function visible(o: object, key: symbol): boolean {
  const descriptor = Object.getOwnPropertyDescriptor(o, key);
  return descriptor !== undefined && descriptor.enumerable;
}
