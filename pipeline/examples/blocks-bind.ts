function closureBlock(seed: boolean): boolean {
  const f = (x: boolean): boolean => {
    const snapshot = x;
    if (snapshot) {
      return seed;
    } else {
      return snapshot;
    }
  };
  return f(seed);
}
function partialApplication(seed: boolean): boolean {
  const choose = (left: boolean, right: boolean): boolean => left;
  const bound = choose.bind(null, seed);
  return bound(false);
}
