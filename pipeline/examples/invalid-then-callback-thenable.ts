// A `then` callback returning an object whose `then` is callable: the native
// `then` resolves the callback's result, calling that `then` (run under Node:
// the result settles to 42), so the callback is refused there.
export function chain(p: Promise<number>): Promise<number> {
  return p.then(() => ({
    then(resolve: (value: number) => void): void {
      resolve(42);
    },
  }));
}
