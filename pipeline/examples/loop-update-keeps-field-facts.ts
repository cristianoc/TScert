// A loop whose update assigns bindings in a comma expression, slots it
// rebinds, and whose body tests `flag && keeps(r)`: a type invariant over
// a local object's number fields holds at each call needing it. Each slot's
// write leaves the fields of the older object `r` alone, the string method
// in the update keeps the heap, and `keeps(r)`, which writes no binding
// named `r`, states the invariant again where it runs (pretext's
// `getBlinkLineBreaks`).

/** @invariant safeInteger(this.count) && 0 < this.count && safeInteger(this.width) && this.width === this.count + 3 */
export type Rules = { count: number; width: number };

export function make(): Rules {
  return { count: 1, width: 4 };
}

export function use(r: Rules): number {
  return r.width - r.count;
}

export function keeps(r: Rules, c: number): boolean {
  return c > r.count;
}

export function walk(text: string, flag: boolean): number {
  const r = make();
  let s = 0;
  let last = 0;
  for (let i = 1; i < text.length; last = text.charCodeAt(i), i++) {
    if (flag && keeps(r, last)) continue;
    s = use(r);
  }
  return s;
}
