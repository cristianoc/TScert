// Two instances of one declaration with generic methods are related through
// those methods: `then` and `catch` are host-relative members with quantified
// signatures binding the same rows, and the target's `then` at
// `number | string` passes its callbacks nothing a `number` one could not
// take. So `Promise` is covariant, and `never` is below every payload.
export function widen(p: Promise<number>): Promise<number | string> {
  return p;
}
export function fromNever(p: Promise<never>): Promise<number> {
  return p;
}
