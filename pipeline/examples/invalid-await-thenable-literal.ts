// `await` of an object literal whose `then` is callable: JavaScript calls the
// `then` with resolving functions and settles to what it passes, here 42
// (run under Node), not the object. The record is neither a native promise
// nor stably non-thenable, so the await is refused.
export async function settle(): Promise<number> {
  const thenable = {
    then(resolve: (value: number) => void): void {
      resolve(42);
    },
  };
  return await thenable;
}
