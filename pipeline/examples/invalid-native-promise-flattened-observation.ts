export async function flattened(
  promise: Promise<Promise<number>>,
): Promise<number> {
  const value: number = await promise;
  return value;
}
