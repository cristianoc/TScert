// An async function typed `Promise<never>`, which shrinks the array it is
// handed before its body throws, called in a `map` callback: a promise is a
// value, so the call returns normally and the callback is bounded by the
// function's footprint, `top` for async code. The result may hold holes and
// is not `number[]` (run under Node: the call pops synchronously, and `map`
// skips the index it removed).
async function stop(xs: number[]): Promise<never> {
  xs.pop();
  throw new Error("stopped");
}

export function wrong(xs: number[]): number[] {
  const r: number[] = xs.map((x) => {
    stop(xs);
    return x;
  });
  return r;
}
