// An array type declaring a `toJSON` member states a hook `JSON.stringify`
// would call: no array has one, own or inherited.
interface Hooked extends Array<number> {
  toJSON(): undefined;
}
export function text(xs: Hooked): string {
  return JSON.stringify(xs);
}
