// A closure parameter TypeScript types from context at a recursive alias,
// directly and as an array's element: read as the alias by name, the
// annotation `Json` would be.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
declare function each(f: (v: Json) => number): void;
function depth(v: Json): number {
  return Array.isArray(v) ? 1 : 0;
}
export function inferred(xs: Json[]): number {
  each((v) => depth(v));
  return xs.map((x) => depth(x)).length;
}
