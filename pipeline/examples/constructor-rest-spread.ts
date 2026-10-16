class Point {
  x: number;
  y: number;
  constructor(x: number = 0, y: number = 0) {
    this.x = x;
    this.y = y;
  }
}
class Labeled {
  label: string;
  n: number;
  constructor(label: string, n: number = 1) {
    this.label = label;
    this.n = n;
  }
}
function build(
  ctor: new (...params: number[]) => Point,
  ...params: number[]
): number {
  const p = new ctor(...params);
  return p.x + p.y;
}
function prefixed(
  ctor: new (label: string, ...rest: number[]) => Labeled,
  xs: number[],
): number {
  return new ctor("a", ...xs).n;
}
function mixed(
  ctor: new (...params: number[]) => Point,
  xs: readonly number[],
): number {
  return new ctor(1, ...xs, 2).y;
}
function grow(xs: number[]): number {
  xs.push(9);
  return 8;
}
function ordered(ctor: new (...params: number[]) => Point): number {
  const xs = [1];
  const p = new ctor(...xs, grow(xs));
  return xs.length * 100 + p.x * 10 + p.y;
}
// A class value flows to a variadic construct signature where the module
// statements pass it.
export const run =
  build(Point, 3, 4) + prefixed(Labeled, [5, 6]) + mixed(Point, []);
export const order = ordered(Point);
