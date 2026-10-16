// A qualified parameter is not its own result: a promise argument resolves.
export async function settle<T extends Resolvable>(value: T): Promise<T> {
  return await value;
}
