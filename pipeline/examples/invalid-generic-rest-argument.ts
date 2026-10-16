// A Boolean actual is not an arbitrary T, even for a rest callback.
function insertsBoolean<T>(emit: (...xs: T[]) => T[]): T[] {
  return emit(true);
}
