// A constructor writing `this.message` after `super`: the message is
// read-only where the instance holds it, so the write is refused.
class Rewritten extends Error {
  constructor(m: string) {
    super(m);
    this.message = `rewritten: ${m}`;
  }
}
export function read(): string {
  return new Rewritten("x").message;
}
