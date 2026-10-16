// A rest parameter typed by a generic alias of an array or a tuple is read
// through the alias's equation at its arguments, as TypeScript reads it.
type RestAlias<E> = readonly E[];
type Pair<A, B> = readonly [A, B];
declare function takesPair<A, B>(...args: Pair<A, B>): B;

export function viaAlias<T>(
  f: (...args: RestAlias<T>) => T,
): (...args: readonly T[]) => T {
  return f;
}

export function pairLayout(
  f: (...args: Pair<number, string>) => string,
): (a: number, b: string) => string {
  return f;
}

export function callPair(): string {
  return takesPair(1, "ok");
}

export function count(...xs: RestAlias<number>): number {
  return xs.length;
}
