function retainOuter(flag: boolean, count: number): number {
  const keep =
    <T>(value: T): (() => T) =>
    (): T =>
      value;
  const later = keep(flag);
  return later() ? keep(count)() : count;
}
