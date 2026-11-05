// An Error subclass's `super(message, {})`: the options are bound at the
// stated options type after the message.
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
