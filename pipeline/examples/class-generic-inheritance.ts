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

class NumBox extends Box<number> {
  constructor(value: number) {
    super(value);
  }
}

class ImplicitNumBox extends Box<number> {}

export function read(n: number): number {
  const base = new Box<number>(n);
  const explicit = new NumBox(n);
  explicit.v = 2;
  const implicit = new ImplicitNumBox(n);
  implicit.v = 3;
  return base.v + explicit.get() + implicit.v;
}

class Pair<X, Y> {
  constructor(
    public first: X,
    public second: Y,
  ) {}
}

class Reordered<A, B> extends Pair<B, A[]> {}

export function readPair(n: number, labels: string[]): number {
  const pair = new Reordered<string, number>(n, labels);
  pair.second = labels;
  return pair.first;
}

class Tagged<Tag extends { tag: string }> {
  constructor(public value: Tag) {}
}

class TaggedBox extends Tagged<{ tag: string }> {}

export function readTag(value: { tag: string }): string {
  return new TaggedBox(value).value.tag;
}

class NullableBox<Value> {
  constructor(public value: Value | null) {}
}

class NullablePrimitive extends NullableBox<number | string> {}

export function readNullable(
  value: number | string | null,
): number | string | null {
  return new NullablePrimitive(value).value;
}
