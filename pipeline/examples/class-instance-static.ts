// A class's static fields are own data properties of the class value: its
// instance methods and constructor, which run only once the class value
// exists, read them late, from the class value they read as the class's own
// binding. Its static methods are bindings bound before its other members,
// which call them; a static initializer calls one whose body does not read
// the class, which the model allocates only after the static initializers.
class Counter {
  static twice(n: number): number {
    return n * 2;
  }
  static make(start: number): Counter {
    return new Counter(start + Counter.step);
  }
  static readonly step: number = Counter.twice(1);
  static readonly label: string = "n";
  n: number;
  constructor(start: number) {
    this.n = start + Counter.step;
  }
  next(): number {
    return Counter.twice(this.n) + Counter.step;
  }
  name(): string {
    return Counter.label;
  }
}

export function use(c: Counter): number {
  return c.next() + new Counter(c.name().length).n + Counter.make(1).n;
}
