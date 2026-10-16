// An optional method of a type literal nested in a declaration has no
// declaration to be received by.
type Outer = { inner: { m?(): number } };
export function read(o: Outer): number {
  return 0;
}
