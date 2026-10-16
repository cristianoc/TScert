type Child = { a?: number; b: number };
export function nested(x: { child: Child | null }): number {
  if (x.child !== null) {
    const {
      child: { a = 0, b },
    } = x;
    return a + b;
  }
  return 0;
}
export function direct(x: { child: Child | null }): number {
  if (x.child !== null) return x.child.b;
  return 0;
}
export function optional(x: { child?: Child | null }): number {
  if (x.child !== undefined && x.child !== null) return x.child.b;
  return 0;
}
export function nullish(x: { child: Child | null | undefined }): number {
  if (x.child != null) return x.child.b;
  return 0;
}
export function reassigned(seed: Child | null): number {
  let child: Child | null = seed;
  if (child !== null) {
    const result = child.b;
    child = null;
    return result;
  }
  return 0;
}
export function snapshot(x: { child: Child | null }): number {
  if (x.child !== null) {
    const { child } = x;
    x.child = null;
    return child.b;
  }
  return 0;
}
