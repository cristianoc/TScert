// `Array.isArray` of `unknown` finds a node list too, a host value: its own
// fields' descriptors are refused (R8, COMPILER-API.md).
export function rowAt(rows: unknown, label: number | string): unknown {
  return Array.isArray(rows)
    ? Object.getOwnPropertyDescriptor(rows, label)?.value
    : undefined;
}
