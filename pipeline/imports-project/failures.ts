// Classes the `instanceof` value-import examples import, each a class
// declaration TypeScript accepts, which `x instanceof C` reads through the
// import (`instanceof-class-value-import`), and the forms it refuses.
export class IoFailure extends Error {
  readonly operation: string;
  constructor(operation: string) {
    super(`${operation} failed`);
    this.operation = operation;
  }
}

export class ParseFailure extends IoFailure {
  readonly line: number;
  constructor(line: number) {
    super("parse");
    this.line = line;
  }
}

export class Pair<T> {
  readonly first: T;
  readonly second: T;
  constructor(first: T, second: T) {
    this.first = first;
    this.second = second;
  }
}

export default class Fault {
  readonly code: number = 1;
}

// A class expression a constant holds
// (`invalid-instanceof-expression-value-import`).
export const Made: new () => { readonly made: boolean } = class {
  readonly made: boolean = true;
};
