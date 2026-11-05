// A mapped type with an `as` clause: no term states the remapped result.
type Renamed = { [K in "x" as `${K}y`]: number };
export function read(r: Renamed): number {
  return r.xy;
}
