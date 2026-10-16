// A class extending a generic class at arguments other than the base's own
// binders: the base's construction is at those binders' rows, and would need
// instantiating at the arguments.
class Box<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
}

class NumberBox extends Box<number> {}

export function use(n: number): number {
  return new NumberBox(n).v;
}
