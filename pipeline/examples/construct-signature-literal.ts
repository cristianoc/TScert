// A type literal of construct signatures only is the constructor type they
// state: `{ new (x: number): T }` is `new (x: number) => T`.
class Point {
  x: number;
  constructor(x: number) {
    this.x = x;
  }
}
declare const Factory: { new (x: number): { x: number } };
function made(): number {
  return new Factory(1).x;
}
function asFactory(): { new (x: number): { x: number } } {
  return Point;
}
