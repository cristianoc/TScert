export async function forward(
  value: Promise<{ n: number }>,
): Promise<{ n: number }> {
  return value;
}
