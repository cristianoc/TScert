// A callback returning the wrong type: `then` instantiates
// `TResult1 := number` through `TResult1 | PromiseLike<TResult1>`, and
// `Promise<number>` is no `Promise<string>`.
export function show(p: Promise<number>): Promise<string> {
  // @ts-expect-error Type 'Promise<number>' is not assignable to type 'Promise<string>'
  return p.then((n: number) => n + 1);
}
