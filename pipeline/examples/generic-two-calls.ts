function instantiateTwice(flag: boolean, count: number): number {
  const id = <T>(value: T): T => value;
  const kept = id(flag);
  return kept ? id(count) : count;
}
