// A member named `cause` of a class extending `Error` stands for the own
// `cause` its options give, which JavaScript keeps non-enumerable and the
// model does not state: refused at the member, as `message` and `stack` are.
class Caused extends Error {
  readonly cause: string = "own";
  constructor(m: string) {
    super(m, { cause: 0 });
  }
}
export function read(): string {
  return new Caused("x").cause;
}
