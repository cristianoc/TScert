// A `let` without an initializer holds `undefined` until assigned: where a
// path into the read left it unassigned, it is not known to hold another
// value, and the failed search is named by that reason.
type Point = { x: number; y: number };

export function pick(b: boolean): Point {
  let p: Point;
  if (b) {
    p = { x: 1, y: 2 };
  }
  // @ts-expect-error p is used before being assigned
  return p;
}
