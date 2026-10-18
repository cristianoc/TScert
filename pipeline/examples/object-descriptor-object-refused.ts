// `object` admits a host object: its own fields' descriptors are refused (R8,
// COMPILER-API.md).
export function fieldOf(o: object, key: string): unknown {
  return Object.getOwnPropertyDescriptor(o, key)?.value;
}
