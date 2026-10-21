export function f<T>(x: T): string {
  type A = { v: T };
  const g = <T>(y: T): string => {
    type B<U> = keyof A;
    const z: B<string> = "v";
    return z;
  };
  return g(x);
}
