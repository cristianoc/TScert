// A compound or logical assignment of an instance field reads and writes
// the field's location, at its contract; the instance's methods and views
// say nothing of it.
class Counter {
  count: number = 0;
  total: number = 0;
  seen: boolean = false;
  add(x: number): number {
    this.count++;
    this.total += x;
    this.seen ||= x > 10;
    return this.total / this.count;
  }
}

export function use(c: Counter): number {
  return c.add(3);
}
