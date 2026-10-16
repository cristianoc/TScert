function capturedStore(flag: boolean, count: number): number {
  let store: number = count;
  const read = <T>(value: T): number => store;
  const first = read(flag);
  const second = read(count);
  return flag ? first : second;
}
