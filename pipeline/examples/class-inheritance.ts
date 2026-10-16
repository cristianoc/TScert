// A derived class: its constructor runs its base's at `super(...)`, whose
// fresh instance's own fields are copied into the derived instance, then its
// own fields over them; its prototype holds the base's methods and its own.
// `super.m()` calls the base's method with the same receiver. An implicit
// constructor passes nothing to a base taking nothing.
class Base {
  name: string;
  constructor(name: string) {
    this.name = name;
  }
  getName(): string {
    return this.name;
  }
  greet(): string {
    return "hello " + this.name;
  }
}
class Derived extends Base {
  age: number;
  constructor(name: string, age: number) {
    const shown = name + "!";
    super(shown);
    this.age = age;
  }
  getAge(): number {
    return this.age;
  }
  greet(): string {
    return super.greet() + ", " + this.getName();
  }
}
class Tagged {
  tag: string = "base";
  hello(): string {
    return this.tag;
  }
}
class Loud extends Tagged {
  extra: number = 1;
  hello(): string {
    return super.hello() + "!";
  }
}
class Louder extends Loud {}
export function main(): string {
  const d = new Derived("a", 1);
  const b: Base = d;
  const l = new Louder();
  const t: Tagged = l;
  return b.getName() + d.getAge() + d.greet() + l.hello() + t.hello() + l.extra;
}
