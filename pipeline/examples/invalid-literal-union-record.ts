// The literal names the `square` kind but carries the circle's key: no arm
// admits it, and the widened `{ kind: string; radius: number }` is neither.
type Shape =
  | { kind: "circle"; radius: number }
  | { kind: "square"; side: number };
export function bad(): Shape {
  return { kind: "square", radius: 1 };
}
