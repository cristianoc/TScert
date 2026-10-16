// A write of `__proto__` runs the prototype's setter: it replaces the
// prototype and adds no key, so it is refused.
export function grow(): {} {
  const o = {};
  o["__proto__"] = { a: 1 };
  return o;
}
