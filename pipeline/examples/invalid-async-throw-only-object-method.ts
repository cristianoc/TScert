// An async method of an object literal whose body reaches no completion,
// called in a `map` callback: its throw rejects the promise its call
// returns, so its footprint is `top` (run under Node: the callee pops
// synchronously, and `map` skips the index it removed).
function fail(xs: number[]): never {
  xs.pop();
  throw new Error("failed");
}

export function wrong(xs: number[]): number[] {
  const runner = {
    async run(ys: number[], stop: (ys: number[]) => never): Promise<number> {
      stop(ys);
      throw new Error("unreached");
    },
  };
  const r: number[] = xs.map((x) => {
    runner.run(xs, fail);
    return x;
  });
  return r;
}
