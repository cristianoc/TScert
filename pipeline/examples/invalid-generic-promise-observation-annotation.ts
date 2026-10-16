export async function annotateObserved<T>(value: T): Promise<Awaited<T>> {
  const observed: Awaited<T> = await value;
  return observed;
}
