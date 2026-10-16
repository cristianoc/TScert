// Pairs built with `as const` and destructured by later callbacks: each
// callback's parameter TypeScript types from its context as
// `readonly [string, number]`, which the closure's contract does not state.
export function counted(
  names: string[],
  count: (name: string) => number,
): string {
  return names
    .map((name) => [name, count(name)] as const)
    .filter(([, n]) => n)
    .map(([name, n]) => `${n} ${name}`)
    .join(", ");
}
