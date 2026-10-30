// A spread of a `ReadonlyMap`'s `values()`, as `mergeRefusal`'s
// `[...interfaceOverlay.values()]` in `array-prototype.mts`: the spread
// keeps the host's collection iteration, `%Spread:Iterator%`, which takes
// only a host `Map`'s or `Set`'s iterator; a program's object meeting the
// view may return any iterator, so the spread is refused where it is typed.
// A loop over the same call runs the iterator protocol
// (`for-of-readonly-map-values`).
export function listed(m: ReadonlyMap<string, number>): number[] {
  return [...m.values()];
}
