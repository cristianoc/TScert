// An error class another module declares, imported by
// blocker-instanceof-imported-class.ts.
export class IoFailure extends Error {
  readonly operation: string;
  constructor(operation: string) {
    super(`${operation} failed`);
    this.operation = operation;
  }
}
