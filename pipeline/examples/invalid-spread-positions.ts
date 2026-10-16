// The second spread's elements start after the first's: its `null` is the
// third argument, where a boolean is taken.
function shiftedSpread(seed: boolean): boolean {
  const one: [boolean] = [seed];
  const two: [boolean, null] = [seed, null];
  const pick = (first: boolean, second: boolean, third: boolean): boolean =>
    third;
  return pick(...one, ...two);
}
