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
function optionalContract(seed: boolean): boolean {
  const pick: (first: boolean, second?: boolean) => boolean = (
    first: boolean,
    second?: boolean,
  ): boolean => {
    if (second === undefined) {
      return first;
    }
    return second;
  };
  return pick(seed);
}

// Optional unknown admits undefined through semantic top, not a literal row.
function omittedUnknown(seed: boolean): boolean {
  const pick = (ignored?: unknown): boolean => seed;
  return pick();
}
