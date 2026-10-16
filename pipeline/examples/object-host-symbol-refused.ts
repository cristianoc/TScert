// A well-known symbol key other than `Symbol.iterator`: `Symbol.toStringTag`
// changes what `Object.prototype.toString` gives, and would let the object
// pass for a host collection, whose iteration is trusted to be the host's.
export function tagged(): object {
  return { [Symbol.toStringTag]: "Set" };
}
