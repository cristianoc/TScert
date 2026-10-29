// A closure at a field whose type has two call signatures, the first
// generic: the closure meets the first and not the second, which promises a
// string where the closure returns its number argument. TypeScript gives
// its parameter no contextual signature, so `any`; the closure is refused.
// Under Node, `library.reviewed(5)` returns the number 5.
interface Reviewer {
  <R>(read: () => R): R;
  (n: number): string;
}
interface Library {
  reviewed: Reviewer;
}
export function used(): string {
  const library: Library = { reviewed: read => (typeof read === "function" ? read() : read) };
  return library.reviewed(5);
}
