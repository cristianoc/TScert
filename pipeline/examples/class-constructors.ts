// A constructor's parameter properties and its `this.f = e` assignments
// initialize the instance, after the field initializers.
class AddIndex {
  constructor(private index: number) {}
  shift(value: number): number {
    return this.index + value;
  }
}
class Point {
  readonly x: number;
  y: number;
  constructor(x: number, y: number) {
    this.x = x;
    this.y = y;
  }
  sum(): number {
    return this.x + this.y;
  }
}
export function use(): number {
  const p = new Point(1, 2);
  const a = new AddIndex(p.sum());
  return a.shift(3);
}
