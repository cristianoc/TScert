type Handle = { advances: (number[] | null)[] };

/**
 * @requires safeInteger(i) && 0 <= i && i < h.advances.length
 */
export function missingDisjunctNonNull(
  h: Handle,
  i: number,
  flag: boolean,
): number {
  const startAdvances: number[] | null | undefined = h.advances[i];
  if (flag || startAdvances !== null) {
    // Unsafe when flag is true and h.advances[i] is null: throws TypeError.
    return startAdvances!.length;
  }
  return 0;
}
