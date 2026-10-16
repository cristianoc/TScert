// A closure's body is a graph, as a function's is: a mutable local and a
// loop inside it.
export function sumTo(n: number): () => number {
  return (): number => {
    let total: number = 0;
    let i: number = 0;
    while (i < n) {
      total = total + i;
      i = i + 1;
    }
    return total;
  };
}
