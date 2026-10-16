function observedCallsOnly(flag: boolean, other: boolean): boolean {
  const pick = <T>(value: T): T => flag;
  const first = pick(flag);
  const second = pick(other);
  return first ? second : flag;
}
