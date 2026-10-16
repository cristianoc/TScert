// Promises about objects: a guard narrowing a discriminated union to one arm
// by a branch on its tag, and a union of a tuple and a number to the tuple; each call
// reads what only the narrowed arm has.
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
  if (s.kind === "circle") return true;
  return false;
}

export function area(s: Shape): number {
  return isCircle(s) ? s.radius * s.radius * 3 : s.kind.length;
}

export type Span = readonly [number, number];

export function isSpan(v: Span | number): v is Span {
  return typeof v !== "number";
}

export function width(v: Span | number): number {
  if (isSpan(v)) return v[1] - v[0];
  return 0;
}
