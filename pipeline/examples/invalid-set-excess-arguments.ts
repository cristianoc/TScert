// `new Set` with an argument past the stated forms' parameters is refused.
export function extra(xs: number[]): number {
  // @ts-expect-error: the constructor takes one argument
  return new Set(xs, 1).size;
}
