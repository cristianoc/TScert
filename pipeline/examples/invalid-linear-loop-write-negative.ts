// A counter from -1: the first write is at "-1", an own property no array
// owns. Under Node, `const xs = [1, 2]; for (let j = -1; j < xs.length; j++)
// xs[j] = 0;` leaves `Object.keys(xs)` as ["0", "1", "-1"].
export function clear(xs: number[]): void {
  for (let j = -1; j < xs.length; j++) {
    xs[j] = 0;
  }
}
