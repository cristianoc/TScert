export async function consumeObserved<T>(
  value: T,
  consume: (result: Awaited<T>) => void,
): Promise<void> {
  consume(await value);
}
