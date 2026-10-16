// A path that leaves the cell unassigned reaches the read holding
// `undefined`: no fact says otherwise (TypeScript rejects the read too).
interface Point {
  x: number;
  y: number;
}

export function onePath(flag: boolean): Point {
  let p: Point;
  if (flag) p = { x: 1, y: 2 };
  // @ts-expect-error p is used before being assigned
  return p;
}
