// A generic class's static fields name none of its binders (TypeScript
// refuses one that does): its class value holds them at each instance, and
// a read of one reads the class value at an instance, each binder at its
// bound.
class Box<T> {
  static readonly limit: number = 3;
  value: T;
  constructor(value: T) {
    this.value = value;
  }
}

export function use(): number {
  return Box.limit + new Box(1).value;
}

export function only(): number {
  return Box.limit;
}
