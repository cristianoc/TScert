// Omit of an interface with a string index signature: TypeScript keeps the
// index and drops the named members; Pick over the keys `string | number`
// is refused.
interface Table {
  [key: string]: number;
  size: number;
}
export function size(t: Omit<Table, "size">): number {
  return 0;
}
