// A computed alias applied at its parameter's default.
type Element<T extends readonly { a: number }[] = readonly { a: number }[]> = T[number];
export function f(x: Element): number {
  return x.a;
}
