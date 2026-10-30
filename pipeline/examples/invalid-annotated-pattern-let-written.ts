// An annotated `let` pattern whose binding is assigned: the annotation
// states `n`'s contract, `1`, which `n++` breaks (run under Node: `f()`
// returns 2).
export function f(): number {
  let [n]: [1] = [1];
  n++;
  return n;
}
