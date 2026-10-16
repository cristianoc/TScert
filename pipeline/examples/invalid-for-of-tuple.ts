// An element of `[string, number]` may be a string.
export function bad(): number {
  const items: [string, number] = ["a", 1];
  let total = 0;
  for (const item of items) {
    const n: number = item;
    total = total + n;
  }
  return total;
}
