// Locals hiding a binding of an enclosing scope: each is its own binding,
// and every reference reads the one TypeScript resolves it to.
const seed: number = 1;

export function inner(): string {
  const seed = "local";
  return seed;
}

export function nested(flag: boolean): number {
  let seed = 2;
  if (flag) {
    const seed = "block";
    const copy: { seed: string } = { seed };
    return copy.seed.length;
  }
  seed = seed + 1;
  return seed;
}

export function closures(): (seed: string) => string {
  const seed = 3;
  const pick = (seed: string): string => seed;
  return seed > 2 ? pick : (s: string): string => s;
}

export function loops(xs: readonly string[]): number {
  let total = seed;
  for (const seed of xs) total = total + seed.length;
  return total;
}

export function outer(): number {
  return seed;
}
