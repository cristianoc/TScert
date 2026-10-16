// A `Box` constructed at `number` holds a number: its `get` returns no string.
class Box<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
  get(): T {
    return this.v;
  }
}

export function use(): string {
  const b = new Box(1);
  return b.get();
}
