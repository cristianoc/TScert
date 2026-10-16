// In a static member `super` is the base's constructor, whose statics are
// bindings of their own: `super.s()` here calls the base's static `s`, not
// the method of the base's prototype of that name. Refused.
class Base {
  s(): number {
    return 1;
  }
  static s(): number {
    return 2;
  }
}
class Derived extends Base {
  static t(): number {
    return super.s();
  }
}

export function use(): number {
  return Derived.t();
}
