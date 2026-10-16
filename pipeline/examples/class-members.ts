// Class members beyond plain fields and methods. `private`, `protected` and
// `public` are TypeScript's alone: at run time each member is an ordinary
// property, so the instance type states it as any other. An optional field
// may be left `undefined` where its type admits it; a definitely-assigned one
// holds its type because the constructor assigns it. An optional parameter
// property is the optional field `x?: T | undefined`.
interface Named {
  readonly name: string;
  alias?: string | undefined;
}
class Counter {
  private count: number = 0;
  protected step: number = 1;
  public label: string = "counter";
  private advance(): number {
    return this.count + this.step;
  }
  next(): number {
    return this.advance();
  }
}
class Person implements Named {
  readonly name: string;
  alias?: string | undefined;
  nickname?: string = "none";
  id!: number;
  constructor(name: string, id: number, alias?: string) {
    this.name = name;
    this.alias = alias;
    this.id = id;
  }
}
class Tagged {
  constructor(
    public tag?: string,
    readonly weight?: number,
  ) {}
  describe(): string | undefined {
    return this.tag;
  }
}
function nameOf(named: Named): string {
  return named.name;
}
export function use(): number {
  const person = new Person("ada", 1);
  const tagged = new Tagged("t", 2);
  const bare = new Tagged();
  const tag: string | undefined = tagged.describe();
  const weight: number | undefined = bare.weight;
  const name: string = nameOf(person);
  return new Counter().next() + person.id;
}
