// A class extending `Array`: its instances' `constructor` is the subclass,
// so `map` constructs its result through the subclass (`ArraySpeciesCreate`),
// which the ordinary array construction assumption excludes. Refused where the
// class is read; `test.mts` runs `doubled` under Node to show the construction.
export class Counted extends Array<number> {}

export function doubled(xs: Counted): number[] {
  return xs.map((x) => x * 2);
}
