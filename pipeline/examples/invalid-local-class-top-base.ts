// A class declared in a method's block extending a top-level class, whose
// lowering the method's may precede: refused at the base.
class Base {
  readonly k: number = 1;
}

class Holder {
  make(): number {
    class Derived extends Base {}
    return new Derived().k;
  }
}

export function use(): number {
  return new Holder().make();
}
