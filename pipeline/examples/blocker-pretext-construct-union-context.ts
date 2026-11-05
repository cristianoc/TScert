// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): measurement.ts#getFontSpaceKerning.
// Refusal: reject: source expression obligation: no derivation of its
// node-typing claim, `new Map()` claimed at `Map<void, void>`.
// A `new Map()` with no type arguments written where a field holding
// `Map<number, number> | null | undefined` is expected: the construction's
// type arguments are inferred from the arm of the expected union naming the
// same declaration, as TypeScript infers to the union member of the same
// reference; the map is fresh and empty, so any instance holds it.
type Measurement = { spaceKerning: Map<number, number> | null | undefined };

export function spaceKerning(
  measurement: Measurement,
  kerned: boolean,
): Map<number, number> | null {
  if (measurement.spaceKerning === undefined)
    measurement.spaceKerning = kerned ? new Map() : null;
  return measurement.spaceKerning;
}
