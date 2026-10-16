// A class's instance members read the class itself: its methods construct
// and test their own class, and its constructor constructs another instance.
// They are created before the class value is bound, and run only once it
// is, so they read the class's own binding, at its construct signature. A
// static member runs once the class value exists and reads it directly; a
// parameter named like the class is not it.
class Point {
  x: number;
  constructor(x: number) {
    this.x = x;
  }
  shifted(d: number): Point {
    return new Point(this.x + d);
  }
  same(o: unknown): boolean {
    return o instanceof Point;
  }
  scaled(Point: number): number {
    return this.x * Point;
  }
  static readonly origin: Point = new Point(0);
  static at(x: number): Point {
    return new Point(x);
  }
}
class Pair {
  first: Point;
  rest: Pair | null;
  constructor(first: Point, more: boolean) {
    this.first = first;
    this.rest = more ? new Pair(first.shifted(1), false) : null;
  }
}
class Labeled extends Point {
  label: string;
  constructor(x: number, label: string) {
    super(x);
    this.label = label;
  }
  renamed(label: string): Labeled {
    return new Labeled(this.x, label);
  }
}
export function use(p: Point): number {
  const q = p.shifted(1);
  const r = Point.at(2);
  const pair = new Pair(q, true);
  const l = new Labeled(1, "a").renamed("b");
  return (
    q.x +
    r.x +
    Point.origin.x +
    pair.first.x +
    l.x +
    p.scaled(2) +
    (p.same(q) ? 1 : 0)
  );
}
