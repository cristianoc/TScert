class Box<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
  get(): T {
    return this.v;
  }
}

class SubBox<T> extends Box<T> {}

class Labeled<T> extends Box<T> {
  label: string;
  constructor(v: T, label: string) {
    super(v);
    this.label = label;
  }
  describe(): string {
    return this.label;
  }
}

export function use(n: number): number {
  const b = new SubBox(n);
  const l = new Labeled(n, "x");
  return b.get() + l.get();
}
