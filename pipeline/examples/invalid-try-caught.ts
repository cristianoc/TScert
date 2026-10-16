// What a handler catches is any value: here the number thrown, but a raise
// from `mayThrow` may carry anything.
function caughtNumber(mayThrow: () => void): number {
  try {
    mayThrow();
    throw 1;
  } catch (e) {
    const n: number = e as number;
    return n;
  }
}
