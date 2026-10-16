// A copy takes a class value's own enumerable properties: the static field
// its base class holds is not among them, though the class reaches it.
class Base {
  static readonly inherited: number = 1;
}
class Derived extends Base {
  static readonly own: number = 2;
}
export function copy(): { inherited: number } {
  return { ...Derived };
}
