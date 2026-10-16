// `catch<TResult>` returns `Promise<T | TResult>`: every call's result adds
// a binder, one application of the one `Promise` equation each. The callback
// returns a number, which TypeScript infers through `TResult |
// PromiseLike<TResult>`.
export function recover(p: Promise<number>): Promise<number> {
  return p.catch((reason: unknown) => 0);
}
