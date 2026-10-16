// A `Point` may own keys its interface does not name, a callable `toJSON`
// among them, which `JSON.stringify` would call and whose result may be
// `undefined`: it is no `JsonValue`, though TypeScript's `any` admits it.
interface Point {
  x: number;
  y: number;
}

function encode(p: Point): string {
  return JSON.stringify(p);
}
