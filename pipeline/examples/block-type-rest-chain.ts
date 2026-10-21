function f<T>(x: T): T[] {
  type A = T[];
  type B = A;
  const g = (...args: B): T[] => args;
  return g(x);
}
