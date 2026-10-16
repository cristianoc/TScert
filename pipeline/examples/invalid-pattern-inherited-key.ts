// A pattern reads as a member access does: an object lacking `valueOf`
// inherits `Object.prototype`'s, a function, so the default does not apply.
export function destructured(o: { valueOf?: number }): number {
  const { valueOf: v = 0 } = o;
  return v;
}
