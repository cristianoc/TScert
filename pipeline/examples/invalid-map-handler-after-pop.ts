// A callback popping the mapped array, then throwing, the throw caught by
// its own handler, which returns normally: the pop happened before the
// exceptional edge, so the result has holes. A node with a handler is outside
// the node-by-node bound, and `map` takes its signature with holes.
export function drained(xs: string[]): string[] {
  return xs.map((x) => {
    try {
      xs.pop();
      throw new Error("stop");
    } catch {
      return x;
    }
  });
}
