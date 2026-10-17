// An array literal of a parameter typed by a named union and a spread of an
// array of it holds that union: its elements are the declaration's, which a
// callback at the declaration takes, so `map` keeps the result dense.
type Shape = { kind: "dot" } | { kind: "line"; length: number };
function size(s: Shape): number {
  return s.kind === "dot" ? 0 : s.length;
}
export function sizes(first: Shape, rest: Shape[]): string {
  return [first, ...rest].map(size).join(", ");
}
