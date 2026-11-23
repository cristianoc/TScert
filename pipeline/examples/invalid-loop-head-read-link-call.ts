type Handle = { xs: number[] };

export function sumViaUnknownFieldWrites(
  h: Handle,
  visit: () => Modifies<{ values: "any"; spines: "keep" }, void>,
): number {
  const xs = h.xs;
  let sum = 0;
  for (let i = 0; i < h.xs.length; i++) {
    sum += xs[i]!;
    visit();
  }
  return sum;
}
