// A value typed `Promise<T>` is assumed to be a built-in promise, never
// fulfilled with a thenable. An object literal the source builds with a
// `then` could pass for one, so it is refused.
export function forged(inner: Promise<number>): Promise<number> {
  const p: Promise<number> = {
    then(onfulfilled?: (value: number) => unknown) {
      return inner.then(onfulfilled);
    },
  } as unknown as Promise<number>;
  return p;
}
