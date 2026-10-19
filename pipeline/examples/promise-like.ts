// `Promise<number>` at `PromiseLike<number>`: the native `then` resolves
// only a native promise or a stable value its callbacks return, where
// `PromiseLike`'s takes a callback returning any thenable, so the native
// contract is no `PromiseLike`.
export function like(p: Promise<number>): PromiseLike<number> {
  return p;
}
