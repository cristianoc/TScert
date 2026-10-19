// An element known only as `unknown` may be an object holding a `toJSON`:
// the array literal around it is no JSON value.
export function text(x: unknown): string {
  return JSON.stringify([x]);
}
