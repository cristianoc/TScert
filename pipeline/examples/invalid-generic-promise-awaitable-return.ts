// An awaitable parameter is no resolvable input: async return resolves it.
export async function forward<T extends Awaitable>(value: T): Promise<unknown> {
  return value;
}
