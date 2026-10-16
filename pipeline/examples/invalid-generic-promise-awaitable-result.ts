// An awaitable parameter owns no result for `Awaited<T>` to name: its
// observation may become thenable, and returning it resolves it again.
export async function settle<T extends Awaitable>(
  value: T,
): Promise<Awaited<T>> {
  const observed = await value;
  return observed;
}
