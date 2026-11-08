// A loop test `i < to || (more && i < xs.length)`: its `true` answer comes
// from either disjunct, and with `to <= xs.length` each bounds `i` by the
// length, so the body's read `xs[i]!` is in bounds (pretext's
// `readScriptRuns`, `runs.read < to || (… && runs.read < text.length)`).

/** @requires safeInteger(i) && 0 <= i && safeInteger(to) && to <= xs.length */
export function sum(xs: number[], i: number, to: number, more: boolean): number {
  let s = 0;
  while (i < to || (more && i < xs.length)) {
    s += xs[i]!;
    i++;
  }
  return s;
}
