// An async return of a class instance whose `then` method is callable: the
// async function's promise adopts it, calling `then` (run under Node: it
// settles to 42), so the return is refused.
class Deferred {
  then(resolve: (value: number) => void): void {
    resolve(42);
  }
}

export async function adopt(): Promise<Deferred | number> {
  return new Deferred();
}
