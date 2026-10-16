// A string key may be `__proto__`, whose setter makes an object value the
// prototype rather than a property: `setProto("__proto__").a` is `"x"`, a
// string where the dictionary promises objects. The copy that adds a key adds
// no prototype. Refused.
export function setProto(key: string): { [k: string]: object } {
  const obj: { [k: string]: object } = {};
  obj[key] = { a: "x" };
  return obj;
}
