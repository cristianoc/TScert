// A call within `{value: any, store: grow}` keeps a lower bound of a length
// wherever it stands: in a declaration, in an assignment, in a test, as the
// right side of `x ??= …` and of a field's `o.f ??= …`.
type Cache = { last: number[] | null };

function add(xs: number[]): Modifies<{ values: "any"; stores: "grow" }, number> {
  xs.push(1);
  return xs.length;
}
function fresh(n: number): number[] {
  return [n];
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function declared(xs: number[], ys: number[], i: number): number {
  const n = add(ys);
  return xs[i]! + n;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function assigned(xs: number[], ys: number[], i: number): number {
  let n = 0;
  n = add(ys);
  return xs[i]! + n;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function tested(xs: number[], ys: number[], i: number): number {
  if (add(ys) > 3) return 0;
  return xs[i]!;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function defaulted(xs: number[], i: number, seen: number[] | null): number {
  let s = seen;
  s ??= fresh(i);
  return xs[i]! + s.length;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function cached(xs: number[], i: number, cache: Cache): number {
  const last = cache.last ??= fresh(i);
  return xs[i]! + last.length;
}
