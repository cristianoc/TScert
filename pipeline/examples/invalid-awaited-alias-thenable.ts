// `Awaited<T>` through an alias at a record with a callable `then`: the
// resolution-qualified binder's instance has no classification, so the call
// is refused (run under Node: the thenable's `then` is called, settling to 42).
type Settled<T> = Awaited<T>;

async function settle<T>(x: T): Promise<Settled<T>> {
  return await x;
}

export function adopted(): Promise<unknown> {
  return settle({
    then(resolve: (value: number) => void): void {
      resolve(42);
    },
  });
}
