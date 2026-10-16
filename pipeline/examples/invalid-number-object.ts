// `Number(o)` of an object runs its `valueOf`, client code that here writes
// `seen.value`: only a primitive is admitted, though TypeScript's
// declaration takes `any`.
export function wrong(o: { a: number }, seen: { value: 0 }): 0 {
  Number(o);
  return seen.value;
}
