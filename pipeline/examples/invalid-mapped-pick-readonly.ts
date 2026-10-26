// `Pick` keeps the modifiers of the fields it picks: `a` stays readonly, so
// a write through an assertion to a writable record is refused.
export function write(p: Pick<{ readonly a: number; b: string }, "a">): void {
  (p as { a: number }).a = 1;
}
