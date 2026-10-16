// `Promise<number>` at `PromiseLike<number>`: the two declarations state
// `then` alike, so their quantified members bind the same rows (a generic
// method's binder rows are its member's), and the covering rule for
// quantified signatures relates them.
export function like(p: Promise<number>): PromiseLike<number> {
  return p;
}
