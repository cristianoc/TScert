// A derived class without a constructor has JavaScript's implicit one,
// `constructor(...args) { super(...args); }`: it takes its base's
// parameters, an optional one included, and passes them on. Methods are
// found along the prototype chain, three classes up.
class Base {
  name: string;
  n: number | undefined;
  constructor(name: string, n?: number) {
    this.name = name;
    this.n = n;
  }
  getName(): string {
    return this.name;
  }
}
class Middle extends Base {
  extra: boolean = true;
  shout(): string {
    return this.getName() + "!";
  }
}
class Leaf extends Middle {}
export function main(): string {
  const m = new Middle("a", 1);
  const l = new Leaf("b");
  const b: Base = l;
  return (
    m.shout() +
    m.getName() +
    l.shout() +
    b.getName() +
    (l.n === undefined ? "" : "?")
  );
}
