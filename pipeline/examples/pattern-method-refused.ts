// A method read off its object by a pattern is not a function value.
class Counter {
  count: number = 0;
  get(): number {
    return this.count;
  }
}
export function extracted(c: Counter): number {
  const { get } = c;
  return get();
}
