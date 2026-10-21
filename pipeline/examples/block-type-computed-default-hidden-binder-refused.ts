export function f<T>(x: T): string {
  type A<U> = keyof { x: T; y: U };
  const g = <T>(y: T): string => {
    type B<U = A<string>> = U;
    const a: B = "x";
    return a;
  };
  return g(x);
}
