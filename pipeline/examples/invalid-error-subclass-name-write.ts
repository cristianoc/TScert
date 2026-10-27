// A constructor's `this.name = …` of a class extending `Error` defines the
// instance's own `name` (run under Node: "Failure"), beside the `name` the
// model states where `Error.prototype` holds it: refused at the write.
class Failure extends Error {
  constructor(message: string) {
    super(message);
    this.name = "Failure";
  }
}

export function main(): string {
  return new Failure("x").name;
}
