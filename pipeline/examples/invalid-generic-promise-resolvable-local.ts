// A program's own `Resolvable` is an ordinary bound, not the qualification:
// the await below has no descriptor for `T`.
type Resolvable = unknown;

export async function settle<T extends Resolvable>(value: T): Promise<unknown> {
  return await value;
}
