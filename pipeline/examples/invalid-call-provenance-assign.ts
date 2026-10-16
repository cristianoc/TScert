// `Object.assign` onto the object replaces its member with a function the
// caller supplies, which may own a `call` property returning a string: the
// copy's `read` is that function, not the literal's arrow.
function probe(f: () => number): number {
  const o = { read: () => 1 };
  Object.assign(o, { read: f });
  const copy = { ...o };
  return copy.read.call(undefined);
}
