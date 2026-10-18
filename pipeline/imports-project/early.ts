// A certified module whose function reads a constant declared after the
// closure that reads it: an early binding of the module's own unit.
export function count(xs: readonly number[]): number {
  let found = 0;
  const visit = (x: number): void => {
    if (wanted(x)) found++;
  };
  const wanted = (x: number): boolean => x > 10;
  for (const x of xs) visit(x);
  return found;
}
