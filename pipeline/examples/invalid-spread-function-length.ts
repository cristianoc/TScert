// A function's `length` is its own property but not an enumerable one: a copy
// does not take it, so the cast TypeScript admits is refused.
export function arity(fn: (a: number, b: number) => number): number {
  const copy = { ...fn } as { length: number };
  return copy.length;
}
