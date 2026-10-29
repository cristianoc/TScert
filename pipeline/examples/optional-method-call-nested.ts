// Optional method calls nested in each other's arguments, and inside
// arrows: each call saves its own object, an inner call's saved object
// hides the outer one's only within the inner call, and an arrow's `this`
// is its enclosing method's (each run under Node).
interface Scope {
  readonly base: number;
  equation?(x: number): number;
}

function current(scope: Scope, log: string[], name: string): Scope {
  log.push(name);
  return scope;
}

// The inner call in the outer call's argument: the outer receiver is the
// outer object after the inner call has saved and used its own.
export function nested(outer: Scope, inner: Scope, x: number, log: string[]): number | undefined {
  return current(outer, log, "outer").equation?.(current(inner, log, "inner").equation?.(x) ?? x);
}

// An arrow whose body is an optional method call on a call.
export function later(scope: Scope, log: string[]): (x: number) => number | undefined {
  return (x: number): number | undefined => current(scope, log, "arrow").equation?.(x);
}

export class Box {
  readonly scope: Scope;
  constructor(scope: Scope) {
    this.scope = scope;
  }
  // An arrow reading the method's `this`: the object is `this.scope`.
  bound(x: number): () => number | undefined {
    return (): number | undefined => this.scope.equation?.(x);
  }
}
