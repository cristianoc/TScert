// A binder bounded by a ground type is the meet of its parameter row and its
// bound: a read through the binder is at the bound, and the binder keeps its
// identity where it is returned.
function len<T extends { length: number }>(x: T): number {
  return x.length;
}
function keep<T extends { length: number }>(x: T): T {
  const y = x;
  return y;
}
function sizes<T extends { size: number }>(b: { value: T }): number {
  return b.value.size;
}
function pairLengths<
  A extends { length: number },
  B extends { length: number },
>(a: A, b: B): [number, number] {
  return [a.length, b.length];
}
export function use(): number {
  return len({ length: 1 }) + sizes({ value: { size: 2 } });
}
