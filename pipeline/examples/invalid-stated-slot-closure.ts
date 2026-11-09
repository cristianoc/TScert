// A binding a closure writes is held in a cell (SOURCE-ELABORATION.md, "Slot
// or cell"): `reset` writes `acc`, so the nested write `acc ??= []` rebinds
// no slot, and the call of `reset` may leave `null` in the cell. TypeScript
// keeps `acc` narrowed past the call; the return of `acc` at `number[]` is
// refused (run under Node: `count()` returns `null`).
export function count(): number[] {
  let acc: number[] | null = null;
  const reset = (): void => {
    acc = null;
  };
  (acc ??= []).push(1);
  reset();
  return acc;
}
