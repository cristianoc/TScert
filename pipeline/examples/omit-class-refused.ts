// Omit of a class instance type is refused: Pick reads no class shape.
class Point {
  x: number = 0;
  y: number = 0;
}
export function y(p: Omit<Point, "x">): number {
  return p.y;
}
