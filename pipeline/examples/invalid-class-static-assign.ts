// `Object.assign` from a class value is refused: the class value's type bounds
// none of its keys, so it may own `__proto__`, which `Object.assign` sets
// through the prototype's setter. JavaScript copies its own static fields.
class Base {
  static readonly inherited: number = 1;
}
class Derived extends Base {
  static readonly own: number = 2;
}
export function assign(): { own: number } {
  return Object.assign({}, Derived);
}
