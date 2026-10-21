export function f<T>(x: T): string {
  type A<U> = U extends string ? { x: T; y: U } : never;
  const g = <T>(y: T): string => {
    const a: keyof A<string> = "x";
    return a;
  };
  return g(x);
}
