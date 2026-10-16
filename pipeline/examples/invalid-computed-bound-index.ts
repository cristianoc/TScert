// An indexed access alias keeps its bound: `number[]` is no
// `readonly string[]`, though TypeScript computes `number` for it.
type ElementOf<T extends readonly string[]> = T[number];
export function f(x: ElementOf<number[]>): number {
  return x;
}
