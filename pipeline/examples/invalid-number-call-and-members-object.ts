// `Number` both called and read through its members keeps its call's
// contract: `Number(o)` of an object runs its `valueOf`, client code, so only
// a primitive is admitted.
export function wrong(o: { a: number }): boolean {
  return Number.isInteger(Number(o));
}
