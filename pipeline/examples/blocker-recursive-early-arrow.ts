// A recursive local arrow an earlier closure calls needs its own reads of
// itself admitted: the earlier closure makes it an early binding.
// Census functions:
// written-applications.mts#writtenApplications.
export function count(k: number): number {
  const run = (n: number): number => down(n);
  const down = (n: number): number => (n <= 0 ? 0 : 1 + down(n - 1));
  return run(k);
}
