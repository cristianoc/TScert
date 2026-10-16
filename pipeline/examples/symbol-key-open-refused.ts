// A symbol key added to an object whose type does not list its keys: the
// copy of an object takes its string keys, and the symbol keys it may own are
// not known. Refused.
export function open(): { a?: number } {
  const obj: { a?: number } = {};
  obj[Symbol.iterator] = () => 1;
  return obj;
}
