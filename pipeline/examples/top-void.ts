function forgetValue(seed: boolean): unknown {
  return seed;
}
function ignoredCallbackResult(seed: boolean): void {
  const actual = (x: boolean): boolean => x;
  const discard: (x: boolean) => void = actual;
  return discard(seed);
}
