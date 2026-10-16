// A readonly field is a view: an update writes no location of it
// (TypeScript rejects the write too).
class Counter {
  readonly count: number = 0;
  add(): number {
    // @ts-expect-error count is readonly
    this.count++;
    return this.count;
  }
}

export function use(c: Counter): number {
  return c.add();
}
