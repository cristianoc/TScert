// A generic method is a host-relative member with quantified signatures: each
// call binds it to its object and names its own instance, here two.
interface Keeper {
  keep<T>(value: T): T;
}
export function both(k: Keeper): string {
  const n: number = k.keep(1);
  const s: string = k.keep("a");
  return n > 0 ? s : "";
}
// Two applications of one declaration relate through their generic methods,
// covariantly in a result.
interface Source<T> {
  read<U>(fallback: U): T | U;
}
export function widen(s: Source<number>): Source<number | string> {
  return s;
}
