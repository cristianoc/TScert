// An async return of an object literal owning a callable `then`: the async
// function's promise adopts it, calling `then` (run under Node: it settles
// to 42), so the return is refused.
export async function adopt(): Promise<unknown> {
  return {
    then(resolve: (value: number) => void): void {
      resolve(42);
    },
  };
}
