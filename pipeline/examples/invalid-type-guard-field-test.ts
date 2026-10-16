// `isCircle` returns the test of the other tag, which TypeScript does not
// check: `radius({ kind: "square", side: 1 })` reads `radius` off a square,
// `undefined`, at `number`.
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
  return s.kind === "square";
}

export function radius(s: Shape): number {
  return isCircle(s) ? s.radius : 0;
}
