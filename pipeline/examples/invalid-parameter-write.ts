// An assigned parameter is a cell at its annotation: `null` is not a number.
function reassigned(n: number, reset: boolean): number | null {
  if (reset) {
    n = null;
  }
  return n;
}
