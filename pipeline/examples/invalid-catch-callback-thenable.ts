// A `catch` callback returning an object whose `then` is callable: the
// native `catch` resolves the callback's result, calling that `then` (run
// under Node: the result settles to 42), so the callback is refused there.
export function recover(p: Promise<number>): Promise<number> {
  return p.catch(() => ({
    then(resolve: (value: number) => void): void {
      resolve(42);
    },
  }));
}
