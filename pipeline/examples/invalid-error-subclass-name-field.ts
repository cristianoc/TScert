// A field `name` of a class extending `Error` is the instance's own (run
// under Node: "Failure"), beside the `name` the model states where
// `Error.prototype` holds it: refused at the member.
class Failure extends Error {
  readonly name: string = "Failure";
}

export function main(): string {
  return new Failure("x").name;
}
