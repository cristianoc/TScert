// `String(o)` of an object runs its `toString`, which may throw: only a
// primitive is admitted, though TypeScript's declaration takes `any`.
function describe(o: { a: number }): string {
  return String(o);
}
