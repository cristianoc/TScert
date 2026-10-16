export function invalid(x: {
  before?: null;
  child: { b: number } | null;
}): number {
  if (x.child !== null) {
    const {
      before = (x.child = null),
      // @ts-expect-error The preceding default can replace child with null.
      child: { b },
    } = x;
    return b;
  }
  return 0;
}
