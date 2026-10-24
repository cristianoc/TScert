// An async function whose parameter default calls a never-returning
// function that shrinks the array and throws: the default runs in the async
// call, whose promise its throw rejects, so the call returns normally.
// Async code's footprint is `top`, so the result may hold holes and is not
// `number[]` (run under Node: the default pops synchronously, and `map`
// skips the index it removed).
function fail(xs: number[]): never {
  xs.pop();
  throw new Error("failed");
}

async function run(xs: number[], n: number = fail(xs)): Promise<number> {
  return n;
}

export function wrong(xs: number[]): number[] {
  const r: number[] = xs.map((x) => {
    run(xs);
    return x;
  });
  return r;
}
