// Fewer parameters, but a narrower one: TypeScript compares method parameters
// both ways, so a class whose method takes only `1` passes as one taking any
// number, and `handle(2, "two")` would reach it.
interface Handler {
  handle(x: number, label: string): number;
}

class Ones {
  handle(x: 1): number {
    return x;
  }
}

const make: new () => Handler = Ones;

export function run(): number {
  return new make().handle(2, "two");
}
