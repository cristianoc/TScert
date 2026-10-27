// A spread copies a `Buffer`'s bytes, its own elements, and not `length`, a
// getter of its prototype chain (run under Node: the copy's `length` is
// `undefined`): the copy states no member, refused.
export function copied(bytes: Buffer): number {
  const copy = { ...bytes };
  return copy.length;
}
