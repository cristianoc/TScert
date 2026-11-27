type Handle = { advances: (number[] | null)[] };

/**
 * @requires safeInteger(i) && 0 <= i && i < h.advances.length
 */
export function missingMergeBranchNonNull(
  h: Handle,
  i: number,
  a: boolean,
  b: boolean,
): number {
  const advances = h.advances;
  let start = 0;
  if (a && advances[i] !== null) {
    start = 1;
  } else if (b) {
    // Missing `advances[i] !== null` on this branch: when a is false, b is true,
    // and advances[i] is null, `advances[i]!.length` throws TypeError.
    start = 2;
  } else {
    return 0;
  }
  const fit = advances[i]!;
  return start + fit.length;
}
