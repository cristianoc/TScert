// The instance a construct signature promises must be the class's.
class Point {
  x: number;
  constructor(x: number) {
    this.x = x;
  }
}
function asFactory(): { new (x: number): { x: string } } {
  // @ts-expect-error Point's x is a number
  return Point;
}
