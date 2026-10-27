// A return of an `Error` subclass at the annotation `Error`: the instance's
// link holds its message and the `name` `Error.prototype` gives it.
// Census functions:
// declaration-graph.mts#importBindings, declaration-graph.mts#useProject,
// written-applications.mts#writtenApplications.
class Failure extends Error {
  constructor(message: string) {
    super(message, {});
  }
}
export function use(): Error {
  return new Failure("failed");
}
