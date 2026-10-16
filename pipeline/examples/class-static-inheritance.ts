// A class value's own enumerable properties are its own static fields: a
// copy and an object pattern's rest take those, not the static field its
// base class holds, which the class reaches through its prototype. A
// `for...in` visits both, strings either way.
class Base {
  static readonly inherited: number = 1;
}
class Derived extends Base {
  static readonly own: number = 2;
  static readonly two: number = 3;
}
export function copy(): { own: number; two: number } {
  return { ...Derived };
}
export function rest(): { two: number } {
  const { own, ...r } = Derived;
  return own === 2 ? r : r;
}
export function keys(): string {
  let s = "";
  for (const k in Derived) s += k + ",";
  return s;
}
