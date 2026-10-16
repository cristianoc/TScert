// Only an array's iterator is known: a record may have any iterator, or none.
export function loop(o: { length: number }): number {
  let n: number = 0;
  for (const x of o) {
    n = n + 1;
  }
  return n;
}
