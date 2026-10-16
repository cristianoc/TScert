function invalidVariance(seed: boolean): boolean {
  const narrow = (x: true): boolean => x;
  const wide: (x: boolean) => boolean = narrow;
  return wide(seed);
}
