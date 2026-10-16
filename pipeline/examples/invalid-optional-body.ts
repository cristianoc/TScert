function unguardedOptional(seed: boolean): boolean {
  const pick = (first: boolean, second?: boolean): boolean => {
    return second;
  };
  return pick(seed, seed);
}
