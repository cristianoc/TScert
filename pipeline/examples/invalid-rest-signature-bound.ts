// A rest in a function type, read through its alias's equation, keeps the
// alias's bound.
type Args<T extends string> = [T];
export function f(g: (...a: Args<number>) => number): number {
  return g(1);
}
