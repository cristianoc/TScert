// An array `Array.isArray` finds in `unknown` is read only: its elements have
// a contract the test does not know, which a push could break.
export function grow(x: unknown): void {
  if (Array.isArray(x)) {
    const y: unknown[] = x;
    y.push(1);
  }
}
