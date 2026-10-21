function f<T>(x: T): T[] {
  type A = T[];
  type B<U = A> = U;
  const b: B = [x];
  return b;
}
