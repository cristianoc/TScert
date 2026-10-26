// Options known only as an object, passed through `super(m, o)`: they may own
// a getter at `cause`, which `Error` runs through `[[Get]]`, client code.
// Refused at the options.
class Failure extends Error {
  constructor(m: string, options: object) {
    super(m, options);
  }
}
export function make(m: string, options: object): string {
  return new Failure(m, options).message;
}
