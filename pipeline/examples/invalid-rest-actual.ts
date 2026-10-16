function collectsNull(seed: boolean): boolean[] {
  const collect = (...rest: boolean[]): boolean[] => rest;
  return collect(seed, null);
}
