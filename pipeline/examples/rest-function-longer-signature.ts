// A function with a rest parameter where a signature binding more parameters
// is expected: its first parameters take the leading actuals and its rest's
// element the further ones, a value known by its type and a module function
// alike.
declare const truthy: (value: unknown, ...rest: unknown[]) => boolean;

export function declared(): (s: string, i: number) => unknown {
  return truthy;
}

function collect(v: unknown, ...more: unknown[]): number {
  return more.length;
}

export function own(): (s: string, i: number, b: boolean) => number {
  return collect;
}
