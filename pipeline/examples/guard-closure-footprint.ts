// A guard closure claims the footprint its body stays within at its promise
// signature too, as a guard declaration does: a `map` callback calling it
// keeps its result dense, and a closure calling it stays within a stated
// footprint.
// Census functions:
// fragment-support.mts#forInEntryReads.
type A = { k: "a"; v: string };
type B = { k: "b"; w: number };
export function tested(vs: (A | B)[], key: string): boolean[] {
  const isA = (e: A | B): e is A => e.k === "a" && e.v === key;
  return vs.map((v) => isA(v));
}
export function collected(vs: readonly (A | B)[], key: string): Within<{ value: "any"; store: "grow" }, A[]> {
  const isA = (e: A | B): e is A => e.k === "a" && e.v === key;
  const out: A[] = [];
  const collect = (e: A | B): void => {
    if (isA(e)) out.push(e);
  };
  for (let i = 0; i < vs.length; i++) {
    const e = vs[i];
    if (e !== undefined) collect(e);
  }
  return out;
}
