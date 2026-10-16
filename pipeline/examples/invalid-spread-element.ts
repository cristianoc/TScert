function mismatchedSpread(seed: boolean): boolean {
  const pair: [boolean, boolean] = [seed, seed];
  const pick = (first: boolean, second: null): boolean => first;
  return pick(...pair);
}
