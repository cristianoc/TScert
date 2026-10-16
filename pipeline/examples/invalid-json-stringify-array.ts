// An array may own keys its type does not state, a callable `toJSON`
// among them, which `JSON.stringify` would call: an array is no
// `JsonValue`.
function encode(xs: number[]): string {
  return JSON.stringify(xs);
}
