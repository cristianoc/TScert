// A guard returning a test of its argument's field: the answer is a test of
// the field's value, which the promise check does not relate to the object
// the field was read from.
export interface Circle {
  kind: "circle";
  radius: number;
}

export interface Square {
  kind: "square";
  side: number;
}

export type Shape = Circle | Square;

export function isCircle(s: Shape): s is Circle {
  return s.kind === "circle";
}
