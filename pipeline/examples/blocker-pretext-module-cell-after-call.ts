// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): measurement.ts#clearMeasurementCaches.
// A module cell tested against `null`, then `Map.prototype.clear` called on a
// `Map` it holds, then a field of the cell written: `clear` states
// `{this.size: scalar}`, a field region disjoint from module cells, so the
// cell's non-null narrowing survives the call and the field write verifies.
type State = { fonts: Map<string, number>; segments: number };

let state: State | null = null;

export function clear(): void {
  if (state === null) return;
  state.fonts.clear();
  state.segments = 0;
}
