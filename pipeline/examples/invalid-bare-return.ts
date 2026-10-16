// A bare `return` returns undefined, which a `number` result does not admit.
function early(x: number | null): number {
  if (x === null) {
    return;
  }
  return x;
}
