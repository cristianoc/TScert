// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// rich-inline.ts#findSegmentSources.
// `Object.isFrozen` of a value that is no host object, here a record naming
// an invariant field: its integrity test runs no code and writes nothing, a
// Boolean.
export function frozen(o: { items: string[] }): boolean {
  return Object.isFrozen(o);
}
