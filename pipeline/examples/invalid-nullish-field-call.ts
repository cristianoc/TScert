export function invalid(
  x: { child: { b: number } | null },
  change: () => void,
): number {
  if (x.child !== null) {
    change();
    return x.child.b;
  }
  return 0;
}
