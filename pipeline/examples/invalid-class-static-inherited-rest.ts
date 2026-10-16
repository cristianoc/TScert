// An object pattern's rest copies a class value's own enumerable properties:
// the static field its base class holds is not among them.
class Base {
  static readonly inherited: number = 1;
}
class Derived extends Base {
  static readonly own: number = 2;
}
export function rest(): { inherited: number } {
  const { own, ...r } = Derived;
  return own === 2 ? r : r;
}
