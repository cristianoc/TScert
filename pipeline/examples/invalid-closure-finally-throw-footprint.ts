// A closure whose finalizer shortens an array it captures only after its
// block throws: its normal return changes no store, its throw does. A `map`
// callback that catches the throw and returns may leave holes, which
// `number[]` does not hold (run under Node: `wrong(a, a)` with
// `a = [1, 2, 3]` pops `a` while `map` reads it, at the throw for `2`, so
// the result has no element at its last index).
// On the single pass, a gap: the single pass refuses code 1's edge from node
// 21 after the finalizer's `log.pop()` before the `map` call, a typing of
// closure codes the pass does not make.
export function wrong(vs: number[], log: number[]): number[] {
  const f = (v: number): number => {
    let failed = true;
    try {
      if (v > 1) throw new Error("large");
      failed = false;
      return v;
    } finally {
      if (failed) log.pop();
    }
  };
  return vs.map((v) => {
    try {
      return f(v);
    } catch {
      return 0;
    }
  });
}
