// An async function whose parameter default calls a never-returning callee
// and whose body only throws: no completion is reachable, and the default's
// throw, like the body's, rejects the promise the call returns, so its
// footprint is `top` (run under Node: the default pops synchronously, and
// `map` skips the index it removed).
function fail(xs: number[]): never {
  xs.pop();
  throw new Error("failed");
}

async function run(xs: number[], n: number = fail(xs)): Promise<number> {
  throw new Error(`unreached ${n}`);
}

export function wrong(xs: number[]): number[] {
  const r: number[] = xs.map((x) => {
    run(xs);
    return x;
  });
  return r;
}
