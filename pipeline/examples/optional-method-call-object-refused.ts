// An optional call of a method whose object is a call: the receiver would be
// read again for the call, running the call twice. Refused.
interface Scope {
  equation?(x: number): number;
}

function current(scope: Scope): Scope {
  return scope;
}

export function apply(scope: Scope, x: number): number | undefined {
  return current(scope).equation?.(x);
}
