// An async function whose body reaches no completion: it calls a
// never-returning callee, then throws. Its graph is a synchronous body's,
// and its throw rejects the promise its call returns, so its footprint is
// `top` (run under Node: the callee pops synchronously, and `map` skips the
// index it removed).
function fail(xs: number[]): never {
  xs.pop();
  throw new Error("failed");
}

async function run(
  xs: number[],
  stop: (xs: number[]) => never,
): Promise<number> {
  stop(xs);
  throw new Error("unreached");
}

export function wrong(xs: number[]): number[] {
  const r: number[] = xs.map((x) => {
    run(xs, fail);
    return x;
  });
  return r;
}
