// A module whose function states a postcondition its body does not meet:
// it returns one element fewer than `@ensures` says, so its own unit is
// refused and its module publishes no entry for it.
/** @ensures result.length === source.length + 1 */
export function breaksOf(source: string): Uint8Array {
  return new Uint8Array(source.length);
}
