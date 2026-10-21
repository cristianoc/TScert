export function f<T>(x: T): number {
  type A = { v: T };
  const g = <T>(y: T): number => {
    type B = { [K in keyof A]: number };
    const z: B = { v: 1 };
    return z.v;
  };
  return g(x);
}
