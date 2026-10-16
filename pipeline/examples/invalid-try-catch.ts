// The handler can be entered after `y = null` and before `y = 1`: a raise
// from `mayThrow` finds `y` null there, though the body ends with a number.
function midTryWrite(mayThrow: () => void): number {
  let y: number | null = 1;
  try {
    y = null;
    mayThrow();
    y = 1;
  } catch {
    const n: number = y;
    return n;
  }
  return 0;
}
