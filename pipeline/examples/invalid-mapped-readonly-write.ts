// `Readonly` makes each field readonly: a write through an assertion to a
// writable record is refused.
export function write(p: Readonly<{ a: number }>): void {
  (p as { a: number }).a = 1;
}
