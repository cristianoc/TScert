export function invalid(
  x: { child: { b: number } | null },
  alias: { child: { b: number } | null },
): number {
  if (x.child !== null) {
    alias.child = null;
    return x.child.b;
  }
  return 0;
}
