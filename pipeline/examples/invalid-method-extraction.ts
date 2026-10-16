// A method promises nothing once read off its object: called on another
// receiver, here `undefined`, `this.count` is a TypeError.
class Counter {
  count: number = 0;
  get(): number {
    return this.count;
  }
}
export function extracted(c: Counter): number {
  const g = c.get;
  return g();
}
