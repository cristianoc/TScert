// A call reads a spread where it is written, before a later argument runs.
// The elements are read once every argument is evaluated, so an argument
// after a spread that runs code, here `grow()`, is refused.
function spreadThenCall(seed: boolean): boolean {
  const pair: [boolean, boolean] = [seed, seed];
  const grow = (): boolean => seed;
  const pick = (first: boolean, second: boolean, third: boolean): boolean =>
    third;
  return pick(...pair, grow());
}
