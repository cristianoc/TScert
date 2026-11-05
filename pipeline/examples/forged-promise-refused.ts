// An object literal with a `then` method asserted through `unknown` to be a
// `Promise<number>`: the operand is claimed at `unknown`, which establishes
// no `Promise<number>`, so the assertion is refused.
export function forged(inner: Promise<number>): Promise<number> {
  const p: Promise<number> = {
    then(onfulfilled?: (value: number) => unknown) {
      return inner.then(onfulfilled);
    },
  } as unknown as Promise<number>;
  return p;
}
