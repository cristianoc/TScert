// An early `let` initialized by an expression other than a literal: its
// type is not stated, so the binding is refused.
export function computed(n: number): number {
  const read = (): number => x;
  let x = n + 1;
  return read();
}
