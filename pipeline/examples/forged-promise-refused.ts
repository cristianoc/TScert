// An object literal with a `then` method asserted to be a `Promise<number>`:
// the native contract requires a prototype holding `Symbol.toStringTag`,
// which no object the program makes owns, so the assertion is refused.
export function forged(inner: Promise<number>): Promise<number> {
  const p: Promise<number> = {
    then(onfulfilled?: (value: number) => unknown) {
      return inner.then(onfulfilled);
    },
  } as unknown as Promise<number>;
  return p;
}
