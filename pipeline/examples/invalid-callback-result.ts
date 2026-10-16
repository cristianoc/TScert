function fabricatedThrough(flag: boolean, count: number): number {
  const pick = <T>(make: () => T): T => flag;
  const chosen = pick((): number => count);
  return flag ? chosen : count;
}
