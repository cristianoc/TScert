// A tuple is an array: `for...of` over it yields the union of its positions,
// `%Iterate%`'s element inferred from each of them.
export function mixed(): number {
  const coords: [number, number, number] = [1, 2, 3];
  let total = 0;
  for (const coord of coords) {
    total = total + coord;
  }
  const items: [string, number, boolean] = ["hello", 42, true];
  for (const item of items) {
    const value: string | number | boolean = item;
  }
  return total;
}
