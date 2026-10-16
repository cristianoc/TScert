declare const Other: unknown;

export async function forward(
  p: Promise<{ tag: number }>,
  cell: { value: number },
): Promise<number> {
  await Promise.resolve.call(Other, p);
  return cell.value;
}
