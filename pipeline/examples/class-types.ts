// A class declares its instance type: fields at their annotations, methods as
// readonly fields whose receiver is the instance.
class Counter {
  count: number = 0;
  readonly label: string = "counter";
  get(): number {
    return this.count;
  }
  bump(by: number): number {
    this.count = by;
    return by;
  }
}
export function read(c: Counter): number {
  return c.get();
}
export function write(c: Counter): number {
  c.count = 1;
  return c.label === "x" ? c.count : c.bump(2);
}
