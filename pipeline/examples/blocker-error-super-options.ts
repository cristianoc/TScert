// Error subclass construction needs the cause options contract on its super
// call.
// Census functions:
// declaration-graph.mts#importBindings, declaration-graph.mts#useProject,
// written-applications.mts#writtenApplications.
class Failure extends Error {
  constructor(message: string) {
    super(message, {});
  }
}
export function use(): string {
  return new Failure("failed").message;
}
