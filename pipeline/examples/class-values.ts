// A class value: its methods are allocated once, as its prototype's; `new`
// allocates an instance from the field initializers. Instances are built in
// module initialization and inside a function.
class Counter {
  count: number = 0;
  readonly label: string = "counter";
  get(): number {
    return this.count;
  }
  bump(by: number): number {
    this.count = by;
    return this.get();
  }
}
const shared: Counter = new Counter();
shared.bump(1);
export function fresh(): number {
  const c = new Counter();
  c.bump(2);
  return c.get();
}
export function read(c: Counter): number {
  return c.get();
}
