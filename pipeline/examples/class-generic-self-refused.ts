// A generic class's method constructing its own class names an instance of
// its binders, which the unit declaring the class reads as parameter rows.
class Box<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
  copy(): Box<T> {
    return new Box(this.v);
  }
}
export function first(b: Box<number>): number {
  return b.copy().v;
}
