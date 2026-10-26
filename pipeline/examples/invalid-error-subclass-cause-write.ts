// A write of `this.cause` after `super(m, { cause })` assigns the instance's
// own `cause`, which JavaScript keeps non-enumerable (run under Node:
// `Object.keys` leaves it out). Refused at the write.
class Caused extends Error {
  constructor(m: string) {
    super(m, { cause: 0 });
    this.cause = 1;
  }
}
export function keys(): string[] {
  return Object.keys(new Caused("x"));
}
