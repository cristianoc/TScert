// An assigned binding of a parameter pattern: its contract is the part of
// the annotation it reads, `1`, which an unannotated `let` would widen to
// `number` (run under Node: `f({ n: 1 })` returns 2). Refused at the gate.
export function f({ n }: { n: 1 }): number {
  // @ts-expect-error 2 is not 1
  n = 2;
  return n;
}
