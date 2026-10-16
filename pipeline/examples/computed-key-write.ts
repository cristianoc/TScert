// A write at a key known only at run time to a local's own object is the
// copy of the object with an allocation at the key over it: one field at a
// singleton key, a dictionary at a family's.
export function multiLiteral(key: "a" | "b"): { a?: number; b?: number } {
  const obj = {};
  obj[key] = 42;
  return obj;
}

// A string key may be `__proto__`: where the object does not own it, the
// write runs the prototype's setter, which with a number changes nothing;
// where it owns it, as a copy of a parsed object may, the write is its copy.
export function dictionary(key: string): { [k: string]: number } {
  const obj: { [k: string]: number } = {};
  obj[key] = 42;
  return obj;
}

export function copied(
  source: { [k: string]: number },
  key: string,
): { [k: string]: number } {
  const obj = { ...source };
  obj[key] = 5;
  return obj;
}

export function numberKey(n: number): { readonly [k: number]: string } {
  const obj: { [k: number]: string } = {};
  obj[n] = "x";
  return obj;
}

// A symbol key: the object, whose type lists its keys, is copied onto the
// allocation at the key, the copy of an object taking its string keys.
export function symbolKey(): { [Symbol.iterator]: () => number } {
  const obj = {};
  obj[Symbol.iterator] = () => 1;
  return obj;
}

// Every local holding the object, a `let`'s cell and a constant bound to it,
// holds the copy with the key.
export function inCellWithAlias(key: string): { [k: string]: number } {
  let obj: { [k: string]: number } = {};
  const ref = obj;
  obj[key] = 1;
  obj = {};
  return ref;
}
