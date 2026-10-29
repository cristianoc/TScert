// An absent method gives `undefined`, which is no `number`.
interface Scope {
  equation?(x: number): number;
}

function current(scope: Scope): Scope {
  return scope;
}

export function wrong(scope: Scope, x: number): number {
  return current(scope).equation?.(x) as number;
}
