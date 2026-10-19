// A method named `stack` below a class extending `Error`: every instance owns
// a string `stack` in Node, which shadows it, so a call of it throws a
// TypeError (run under Node). Refused at the member.
class Located extends Error {}

class Traced extends Located {
  // @ts-expect-error a method where `Error` declares a property
  stack(): string {
    return "ok";
  }
}

export function trace(): string {
  return new Traced("x").stack();
}
