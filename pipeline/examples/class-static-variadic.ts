// A class with a static field meets a construct type with a variadic
// construct signature and a readonly property: the class value holds the
// field, and `new` through the type spreads an array into its rest.
class Point {
  static readonly origin: number = 7;
  x: number;
  y: number;
  constructor(x: number = 0, y: number = 0) {
    this.x = x;
    this.y = y;
  }
}
function build(
  ctor: { new (...params: number[]): Point; readonly origin: number },
  xs: number[],
): number {
  return new ctor(...xs).x + ctor.origin;
}
function plain(ctor: new (...params: number[]) => Point, xs: number[]): number {
  return new ctor(...xs).y;
}
export const run = build(Point, [1, 2]) + plain(Point, [3, 4]) + Point.origin;
export function copy(): number {
  const c = { ...Point };
  return c.origin;
}
