// A primitive key makes native WeakMap.set throw TypeError.
export function wrong(): void {
  const table = new WeakMap<object, number>();
  table.set(1, 7);
}
