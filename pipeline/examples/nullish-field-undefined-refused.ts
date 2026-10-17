export function invalid(x: { child?: { b: number } | null }): number {
  if (x.child !== null) {
    // @ts-expect-error The null check permits an absent child.
    return x.child.b;
  }
  return 0;
}
