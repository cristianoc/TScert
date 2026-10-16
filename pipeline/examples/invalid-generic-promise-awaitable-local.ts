// A program's own `Awaitable` is an ordinary bound, not the qualification:
// the await below has no observation for `T`.
type Awaitable = unknown;

export async function settle<T extends Awaitable>(value: T): Promise<unknown> {
  return await value;
}
