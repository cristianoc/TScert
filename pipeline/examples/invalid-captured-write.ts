function capturedWrite(flag: boolean, count: number): number {
  let store: number = count;
  const write = <T>(value: T): T => (store = value);
  const first = write(flag);
  return first ? write(count) : store;
}
