// An awaitable parameter's observation is no resolvable input: returning it
// from an async function resolves it again.
export async function settle<T extends Awaitable>(value: T): Promise<unknown> {
  const observed = await value;
  return observed;
}
