// A function declaration bound after another that mentions it is an early
// binding, and it calls itself: `countdown` reads its own binding, a cell
// initialized before either closure is called (SOURCE-ELABORATION.md,
// "Function declarations in a body"; run under Node: 0).
export function start(): number {
  return relay(2);
  function relay(n: number): number {
    return countdown(n);
  }
  function countdown(n: number): number {
    if (n > 0) return countdown(n - 1);
    return 0;
  }
}
