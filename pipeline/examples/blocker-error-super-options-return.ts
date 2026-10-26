// A return of an `Error` subclass at the annotation `Error` needs the modeled
// error to meet TypeScript's `Error`, which declares `name`.
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
