export function f<T>(x: T): string {
  type A<U> = keyof { x: T; y: U };
  const g = <T>(y: T): string => {
    const a: A<string> = "x";
    return a;
  };
  return g(x);
}
