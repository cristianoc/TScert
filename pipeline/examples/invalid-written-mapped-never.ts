// A mapped type over no key keeps the bound of the application in its value.
type B<T extends string> = T;
export function f(x: { [K in never]: B<number> }): number {
  return 1;
}
