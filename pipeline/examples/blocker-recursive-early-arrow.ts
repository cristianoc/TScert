// A recursive local arrow an earlier closure calls reads itself through its
// early binding's cell, also in one arm of a conditional or a logical
// operator.
// Census functions:
// written-applications.mts#writtenApplications.
export function count(k: number): number {
  const run = (n: number): number => down(n);
  const down = (n: number): number => (n <= 0 ? 0 : 1 + down(n - 1));
  return run(k);
}
export function ternary(n: number): boolean {
  const isEven = (k: number): boolean => (k === 0 ? true : isOdd(k - 1));
  const isOdd = (k: number): boolean => k === 0;
  return isEven(n);
}
export function disjunction(n: number): boolean {
  const isEven = (k: number): boolean => k === 0 || isOdd(k - 1);
  const isOdd = (k: number): boolean => k === 0;
  return isEven(n);
}
