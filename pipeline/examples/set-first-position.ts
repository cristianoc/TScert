// The first of a list of positions, where every later one equals it and it
// is not negative: the equivalent form of an array pattern over a `Set`
// (SOURCE-REWRITES.md, "An array pattern over a `Set`").
// Census functions:
// type-probe.mts#makeProbe
export function onePosition(positions: readonly number[]): number | null {
  let index: number | undefined;
  let one = true;
  for (const at of positions) {
    if (index === undefined) index = at;
    else if (at !== index) one = false;
  }
  return one && index !== undefined && index >= 0 ? index : null;
}
