// Pairs built with `as const` and destructured by later callbacks: each
// callback's parameter TypeScript types from its context as
// `readonly [string, number]`, a tuple, read as its annotation would be.
export function counted(names: string[], counts: Map<string, number>): string {
  const count = (name: string): number => counts.get(name) ?? 0;
  return names
    .map((name) => [name, count(name)] as const)
    .filter(([, n]) => n)
    .map(([name, n]) => `${n} ${name}`)
    .join(", ");
}

// A rest, from a parameter's tuple type.
export function width(
  each: (f: (row: [string, ...boolean[]]) => number) => number,
): number {
  return each((row) => row[0].length);
}
