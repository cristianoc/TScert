function joinedArguments(flag: boolean): boolean {
  const second = <T>(first: T, last: T): T => last;
  return second(true, flag);
}

function upperBoundFromChosenDependency(): (arg: true) => boolean {
  const choose = <U, T extends U>(
    seed: U,
    use: (arg: T) => boolean,
  ): ((arg: T) => boolean) => use;
  return choose(true, (b: boolean): boolean => b);
}

function callbackUpperBounds(): (arg: true) => boolean {
  const choose = <T>(
    first: (arg: T) => boolean,
    last: (arg: T) => boolean,
  ): ((arg: T) => boolean) => last;
  return choose(
    (b: boolean): boolean => b,
    (t: true): boolean => t,
  );
}
