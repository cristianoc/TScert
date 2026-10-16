// `isCircle` answers `true` for squares, which TypeScript does not check:
// `radius(square)` reads `radius` off a square, `undefined`, at `number`.
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
  if (s.kind === "square") return true;
  return false;
}

export function radius(s: Shape): number {
  return isCircle(s) ? s.radius : 0;
}
