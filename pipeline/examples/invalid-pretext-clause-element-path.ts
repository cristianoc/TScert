// An inclusive element-length bound permits a read at the array length.
/**
 * @requires safeInteger(index) && 0 <= index && index < xs.length
 * @requires forall i in xs: xs[i].length <= bounds.length
 */
export function byLength(
  xs: string[],
  bounds: number[],
  index: number,
): number {
  const text = xs[index]!;
  return bounds[text.length]! + 1;
}
