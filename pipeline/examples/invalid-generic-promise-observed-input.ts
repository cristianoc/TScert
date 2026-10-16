export async function unwrap<T>(value: T): Promise<Awaited<T>> {
  const observed: T = await value;
  return observed;
}
