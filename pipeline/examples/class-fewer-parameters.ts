// A class whose method takes fewer parameters than the signature it meets:
// calls through the member discard the extra actuals, so the class value is
// claimed at a construct signature giving the interface, and the method's body
// is checked at the longer signature too.
interface Handler {
  handle(x: number, label: string): number;
}

class Twice {
  handle(x: number): number {
    return x * 2;
  }
}

const make: new () => Handler = Twice;

export function run(): number {
  return new make().handle(1, "one");
}
