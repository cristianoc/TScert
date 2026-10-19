// Another module of the project merges `shout(): string` into `String`, a
// member `String.prototype` does not hold: a string's member read loads its
// prototype contract, and is refused there.
export function upper(s: string): string {
  return s.toUpperCase();
}
