function fabricatedOverload(seed: boolean): true {
  const pick: ((x: boolean) => true) & ((x: null) => null) = (
    x: boolean | null,
  ): boolean | null => {
    if (x === null) {
      return null;
    }
    return x;
  };
  return pick(seed);
}
