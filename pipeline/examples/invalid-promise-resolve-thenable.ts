// `Promise.resolve` of an object literal whose `then` is callable: the
// resolution calls it (run under Node: the promise settles to 42, not the
// object), so the call is refused.
export function wrap(): Promise<unknown> {
  return Promise.resolve({
    then(resolve: (value: number) => void): void {
      resolve(42);
    },
  });
}
