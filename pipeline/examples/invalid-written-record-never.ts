// `Record` over no key keeps the bound of the application in its value.
type B<T extends string> = T;
export function f(x: Record<never, B<number>>): number {
  return 1;
}
