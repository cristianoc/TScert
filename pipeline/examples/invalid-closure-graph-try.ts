// The handler's binding is `unknown`: anything may be thrown, so returning
// it does not give a number.
export function leaks(g: () => number): () => number {
  return (): number => {
    try {
      return g();
    } catch (e) {
      return e as number;
    }
  };
}
