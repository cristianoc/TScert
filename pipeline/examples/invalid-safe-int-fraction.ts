// A fraction returned where `SafeInt` is declared: `0.5` is no integer, so
// the return is refused. The refusal is of the type contract, not of a run.
export function half(): SafeInt {
  return 0.5;
}
