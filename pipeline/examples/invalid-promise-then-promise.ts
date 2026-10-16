// A callback returning a promise of the wrong type: through
// `PromiseLike<TResult1>` it instantiates `TResult1 := number`, and
// `Promise<number>` is no `Promise<string>`.
export function show(p: Promise<number>): Promise<string> {
  // @ts-expect-error Type 'Promise<number>' is not assignable to type 'Promise<string>'
  return p.then((n: number) => Promise.resolve(n));
}
