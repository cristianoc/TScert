function omittedDefault(seed: boolean): boolean {
  const pick = (first: boolean, second: boolean = true): boolean => {
    if (second) {
      return first;
    }
    return second;
  };
  return pick(seed);
}
function writtenArgument(seed: boolean): boolean {
  const pick = (first: boolean, second: boolean = true): boolean => {
    if (second) {
      return first;
    }
    return second;
  };
  return pick(seed, false);
}
function dependentDefault(seed: boolean): boolean {
  const pick = (first: boolean, second: boolean = first): boolean => second;
  return pick(seed);
}
