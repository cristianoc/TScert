// A template of a `Buffer` converts it by its `toString`, a member of the
// host's prototype the conversion contract does not cover: refused.
export function text(b: Buffer): string {
  return `${b}`;
}
