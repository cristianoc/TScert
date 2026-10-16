function omittedArgument(seed: boolean): boolean {
  const pick = (first: boolean, second?: boolean): boolean => {
    if (second === undefined) {
      return first;
    }
    return second;
  };
  return pick(seed);
}
function writtenArgument(seed: boolean): boolean {
  const pick = (first: boolean, second?: boolean): boolean => {
    if (second === undefined) {
      return first;
    }
    return second;
  };
  return pick(seed, seed);
}
function explicitUndefined(seed: boolean): boolean {
  const pick = (first: boolean, second?: boolean): boolean => {
    if (second === undefined) {
      return first;
    }
    return second;
  };
  return pick(seed, undefined);
}
