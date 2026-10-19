// `new Promise`'s resolver given an object whose `then` is callable: the
// resolution calls it (run under Node: the promise settles to 42). The
// stated resolver takes a primitive, so an executor calling it at a
// `PromiseLike` is refused.
export function make(): Promise<number> {
  return new Promise<number>(
    (resolve: (value: number | PromiseLike<number>) => void) =>
      resolve({
        then(inner: (value: number) => void): void {
          inner(42);
        },
      }),
  );
}
