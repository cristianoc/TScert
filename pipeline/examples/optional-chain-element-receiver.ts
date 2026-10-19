// Optional chains whose first receiver is an element read, each link a chain
// of its own: the inner chain's saved receiver and the outer's share one
// name, and a predicate recorded for the inner one is not read as the outer's.
interface F {
  arrows?: number[];
}
export function first(fs: F[]): number | undefined {
  return fs[0]?.arrows?.[0];
}
export function present(fs: F[]): boolean {
  if (fs[0]?.arrows?.[0]) return true;
  return false;
}
