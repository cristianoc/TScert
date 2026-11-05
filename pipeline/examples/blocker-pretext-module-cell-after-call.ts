// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): measurement.ts#clearMeasurementCaches.
// Refusal: reject: source expression obligation: no derivation of its
// node-typing claim, a write at a module cell's contract.
// A module cell tested against `null`, then a method of a `Map` it holds
// called, then a field of the cell written: the call may write any location
// its receiver's store is not known apart from, and a module's cell is
// separated from no location, so past the call the cell is read at its
// contract, `State | null`.
type State = { fonts: Map<string, number>; segments: number };

let state: State | null = null;

export function clear(): void {
  if (state === null) return;
  state.fonts.clear();
  state.segments = 0;
}
