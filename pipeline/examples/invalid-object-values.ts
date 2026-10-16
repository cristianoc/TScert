// A `Point` may own keys its interface does not name, of any value, so
// `Object.values` of one is not a `number[]`, though TypeScript's `any[]`
// result lets it be claimed as one.
interface Point {
  x: number;
  y: number;
}

function coordinates(p: Point): number[] {
  return Object.values(p);
}
