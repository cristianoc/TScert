// An async function returning its never-returning callee's result, called
// in a `map` callback with a callee that shrinks the array and throws: the
// callee's call never returns normally, but an async call returns its
// promise where its body throws, rejected. Async code's footprint is `top`,
// so the result may hold holes and is not `number[]` (run under Node: the
// callee pops synchronously, and `map` skips the index it removed).
function fail(xs: number[]): never {
  xs.pop();
  throw new Error("failed");
}

async function run(
  xs: number[],
  stop: (xs: number[]) => never,
): Promise<number> {
  return stop(xs);
}

export function wrong(xs: number[]): number[] {
  const r: number[] = xs.map((x) => {
    run(xs, fail);
    return x;
  });
  return r;
}
