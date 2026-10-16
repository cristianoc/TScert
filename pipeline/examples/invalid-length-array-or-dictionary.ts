// A dictionary's `length` is an entry it may lack: `size({})` is `undefined`,
// although TypeScript types the read `number`.
export function size(x: number[] | Record<string, number>): number {
  return x.length;
}
