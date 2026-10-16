// A callback returning a promise: `then` instantiates `TResult1 := string`
// through `PromiseLike<TResult1>`, which the callback's `Promise<string>` is.
export function show(p: Promise<number>): Promise<string> {
  return p.then((n: number) => Promise.resolve(n.toString()));
}
// `catch`'s callback returning a promise: `TResult := number` through
// `PromiseLike<TResult>`.
export function recover(p: Promise<number>): Promise<number> {
  return p.catch((reason: unknown) => Promise.resolve(0));
}
