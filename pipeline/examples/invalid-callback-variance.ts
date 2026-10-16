function reversedCallback(flag: boolean, count: number): number {
  const apply = <T>(value: T, use: (arg: T) => number): number => use(value);
  return apply(flag, (n: number): number => n);
}
