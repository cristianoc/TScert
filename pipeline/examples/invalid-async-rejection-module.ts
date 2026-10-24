// An async function returning a module function's never-returning call,
// which shrinks the array and throws: an async call returns its promise
// where its body throws, rejected. Async code's footprint is `top`, so the
// result may hold holes and is not `number[]` (run under Node: the call pops
// synchronously, and `map` skips the index it removed).
function fail(xs: number[]): never {
  xs.pop();
  throw new Error("failed");
}

async function run(xs: number[]): Promise<number> {
  return fail(xs);
}

export function wrong(xs: number[]): number[] {
  const r: number[] = xs.map((x) => {
    run(xs);
    return x;
  });
  return r;
}
