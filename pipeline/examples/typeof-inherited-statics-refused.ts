// `typeof Derived` of a class inheriting a base's static field, as a
// parameter's annotation: the translation refuses it, whatever the unit does
// with the value, as its type would drop the inherited member.
class Base {
  static readonly inherited: number = 1;
}
class Derived extends Base {
  static readonly own: number = 2;
}
export function own(D: typeof Derived): number {
  return D.own;
}
