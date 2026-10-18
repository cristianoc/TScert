// A constant whose arrow calls itself reads the binding inside its own
// initializer: refused at the read until recursive bindings are supported.
export function depth(n: number): number {
  const visit = (k: number): number => (k <= 0 ? 0 : 1 + visit(k - 1));
  return visit(n);
}
