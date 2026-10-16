// Inside a closure as at the top level, a tuple's element has its own type.
export function second(pair: [number, string]): () => number {
  return (): number => pair[1];
}
