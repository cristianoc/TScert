function fabricatedDefault(seed: boolean): boolean {
  const pick = (first: boolean, second: boolean = null): boolean => {
    if (second) {
      return first;
    }
    return second;
  };
  return pick(seed);
}
