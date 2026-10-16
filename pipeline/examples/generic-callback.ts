function throughCallback(flag: boolean, count: number): number {
  const apply = <T>(value: T, use: (arg: T) => number): number => use(value);
  const first = apply(flag, (b: boolean): number => count);
  const second = apply(count, (n: number): number => n);
  return flag ? first : second;
}

function throughResult(flag: boolean, count: number): number {
  const pick = <T>(make: () => T): T => make();
  const chosen = pick((): number => count);
  return flag ? chosen : count;
}
