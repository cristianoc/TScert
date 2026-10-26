// A mapped type at a named type with a call signature: TypeScript maps only
// its members and drops the signature, a reading the reader refuses.
interface Counter {
  (): number;
  count: number;
}
export function count(c: Partial<Counter>): number {
  return c.count ?? 0;
}
