// A constructor may assign only fields without an initializer, once each.
class Point {
  y: number = 0;
  constructor(y: number) {
    this.y = y;
  }
}
export function make(): number {
  return new Point(1).y;
}
