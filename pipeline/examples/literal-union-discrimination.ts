// A fresh object or array literal expected at a union of several records or
// tuples is built at the one arm its keys, length and literal members select,
// as TypeScript discriminates a contextual union.
type Shape =
  | { kind: "circle"; radius: number }
  | { kind: "square"; side: number };

export function circle(r: number): Shape {
  return { kind: "circle", radius: r };
}

function area(s: Shape): number {
  if (s.kind === "circle") return s.radius;
  return s.side;
}
export function square(): number {
  const s: Shape = { kind: "square", side: 2 };
  return area(s);
}
export function passed(): number {
  return area({ kind: "circle", radius: 1 });
}

// The keys alone select an arm; the other arm's `k: boolean` is not assumed.
export function byKeys(): { a: number; k: boolean } | { b: string; k: true } {
  return { b: "s", k: true };
}

export function pair(): [number, string] | [boolean, number] {
  return [true, 0];
}

export function short(): [number, string] | [boolean] {
  return [false];
}
