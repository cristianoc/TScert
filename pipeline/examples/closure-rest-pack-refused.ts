// The local closure collects number elements; its public count operation
// needs the number of the two arguments it supplies.
export function count(): number {
  const bare = (...args: number[]): number => args.length;
  return bare(1, 2);
}
