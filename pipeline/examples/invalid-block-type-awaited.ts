export async function test<T>(x: T): Promise<Awaited<T>> {
  type Awaited<U> = U extends unknown ? number : never;
  const y: Awaited<T> = await x;
  return y;
}
