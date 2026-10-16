function capturedOuter(flag: boolean, count: number): number {
  const keep =
    <T>(value: T): (() => T) =>
    (): T =>
      flag;
  const later = keep(flag);
  return later() ? keep(count)() : count;
}
