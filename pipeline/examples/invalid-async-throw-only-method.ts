// An async method whose body reaches no completion, called in a `map`
// callback: its throw rejects the promise its call returns, so its footprint
// is `top` (run under Node: the callee pops synchronously, and `map` skips
// the index it removed).
function fail(xs: number[]): never {
  xs.pop();
  throw new Error("failed");
}

export class Runner {
  async run(xs: number[], stop: (xs: number[]) => never): Promise<number> {
    stop(xs);
    throw new Error("unreached");
  }
}

export function wrong(runner: Runner, xs: number[]): number[] {
  const r: number[] = xs.map((x) => {
    runner.run(xs, fail);
    return x;
  });
  return r;
}
