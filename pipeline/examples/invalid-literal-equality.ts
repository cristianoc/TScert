// A Boolean singleton test keeps `true` on its true edge, never `false`.
function booleanTag(b: boolean): number {
  if (b === true) {
    const f: false = b;
    return 0;
  }
  return 1;
}
