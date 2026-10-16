// A static field read through a class that inherits it from its base: the
// class value reaches it through its prototype, the base class value, which
// the model's class value does not hold. Safe in JavaScript, refused here.
class Base {
  static readonly inherited: number = 1;
}
class Derived extends Base {
  static readonly own: number = 2;
}
export function read(): number {
  return Derived.inherited + Derived.own;
}
