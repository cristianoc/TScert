// A read of an array at an index computed from its length, `xs[xs.length -
// 1]`, is the host's `%ElementAt%`: the element at an index below the length,
// else `undefined`, an empty array's included. The read is at `T |
// undefined` whatever ran between the length's read and the element's: a
// `pop`, a callback, a write through an alias.
export function last(xs: readonly string[]): string | undefined {
  return xs[xs.length - 1];
}

export function lastOr(xs: readonly string[], fallback: string): string {
  return xs[xs.length - 1] ?? fallback;
}

export function lastLength(xs: readonly string[]): number {
  const item = xs[xs.length - 1];
  if (item !== undefined) return item.length;
  return 0;
}

export function afterPop(xs: string[]): string | undefined {
  const n = xs.length;
  xs.pop();
  return xs[n - 1];
}

export function throughCallback(
  xs: string[],
  f: () => void,
): string | undefined {
  const n = xs.length;
  f();
  return xs[n - 1];
}

export function sparseLast(xs: readonly (string | undefined)[]): string {
  return xs[xs.length - 1] ?? "";
}

export function pastTheEnd(xs: readonly number[]): number | undefined {
  return xs[xs.length];
}
