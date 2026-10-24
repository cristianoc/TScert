// An async function expression whose body reaches no completion, called in
// a `map` callback: its throw rejects the promise its call returns, so its
// footprint is `top` (run under Node: the callee pops synchronously, and
// `map` skips the index it removed).
function fail(xs: number[]): never {
  xs.pop();
  throw new Error("failed");
}

export function wrong(xs: number[]): number[] {
  const run = async function (
    ys: number[],
    stop: (ys: number[]) => never,
  ): Promise<number> {
    stop(ys);
    throw new Error("unreached");
  };
  const r: number[] = xs.map((x) => {
    run(xs, fail);
    return x;
  });
  return r;
}
