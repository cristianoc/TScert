// An unannotated `let` stores what TypeScript declares for it: its
// initializer's type, widened. `value` is a boolean cell, so `null` is not
// written, though the function's result would admit it.
function implicitStorage(seed: boolean): boolean | null {
  let value = seed;
  value = null;
  return value;
}
