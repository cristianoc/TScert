// `Awaited<T>` through an alias qualifies `T` as written: the generic async
// function resolves its parameter, and a stable instance verifies.
type Settled<T> = Awaited<T>;

async function settle<T>(x: T): Promise<Settled<T>> {
  return await x;
}

export function numbers(n: number): Promise<number> {
  return settle(n);
}
