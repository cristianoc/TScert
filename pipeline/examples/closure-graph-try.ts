// A closure's `try`: a throw out of its body goes to its handler, which
// binds what was thrown at `unknown`.
export function guarded(g: () => number): () => number {
  return (): number => {
    try {
      return g();
    } catch (e) {
      return 0;
    }
  };
}
