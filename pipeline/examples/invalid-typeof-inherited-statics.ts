// `typeof Derived` states the static field Derived inherits from Base: a
// class value with only Derived's own static field does not meet it, and the
// annotation, whose class value's type would state only `own`, is refused.
class Base {
  static readonly inherited: number = 1;
}
class Derived extends Base {
  static readonly own: number = 2;
}
class Other {
  static readonly own: number = 2;
}
export function make(): typeof Derived {
  // @ts-expect-error Other lacks the inherited static
  return Other;
}
