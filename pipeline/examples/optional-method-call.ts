// An optional call of a method, `o.m?.(a)`: the member read once and tested,
// `undefined` where it is null or undefined, else called with `o` as its
// receiver; the arguments run only where it is called (run under Node: a
// method reading `this` sees `o`, and an absent one leaves the argument
// unevaluated).
interface Scope {
  readonly base: number;
  equation?(x: number): number;
}

export function apply(
  scope: Scope,
  x: number,
  log: string[],
): number | undefined {
  return scope.equation?.((log.push("argument"), x));
}

export function withDefault(scope: Scope, x: number): number {
  return scope.equation?.(x) ?? x;
}

export function make(base: number): Scope {
  return { base, equation: (x: number): number => base + x };
}
