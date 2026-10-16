export async function consume<T>(
  promise: Promise<T>,
  use: (value: T) => number,
): Promise<number> {
  const value = await promise;
  return use(value);
}

export async function callable(
  promise: Promise<() => number>,
): Promise<number> {
  const value = await promise;
  return value();
}

export async function nested(
  promise: Promise<Promise<number>>,
): Promise<number> {
  const inner = await promise;
  return await inner;
}
