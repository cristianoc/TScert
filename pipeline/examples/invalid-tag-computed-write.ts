// A key-adding write at a key typed `symbol`, which may be
// `Symbol.toStringTag`: refused, as no object the program makes holds the
// tag (run under Node: with the tag as the key, `Object.prototype.toString`
// reports the object as a promise).
export function tagged(s: symbol): { [k: symbol]: string } {
  const d: { [k: symbol]: string } = {};
  d[s] = "Promise";
  return d;
}
