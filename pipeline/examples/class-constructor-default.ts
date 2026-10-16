// Constructor parameters with defaults: the default replaces an omitted or
// undefined argument first in the constructor's code, as a closure's default
// does; one reads an earlier parameter, a parameter property holds the
// defaulted value, and an implicit derived constructor forwards the base's.
class Counter {
  constructor(
    public start: number = 0,
    public step: number = start + 1,
  ) {}
}
class Labeled {
  label: string;
  constructor(prefix: string, suffix: string = "!") {
    this.label = prefix + suffix;
  }
}
class Derived extends Counter {}
export function make(): number {
  const a = new Counter();
  const b = new Counter(2);
  const c = new Counter(3, undefined);
  const d = new Derived(4);
  const l = new Labeled("x");
  return a.start + b.step + c.step + d.step + l.label.length;
}
