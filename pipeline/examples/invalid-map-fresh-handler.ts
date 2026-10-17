// A callback popping a fresh array inside `try`: a handler could resume
// after mutation the bound does not track, so the node-by-node bound refuses
// it and `map` takes its signature with holes, though this run keeps the
// result dense.
export function firsts(xs: string[]): string[] {
  return xs.map((x) => {
    const a = x.split("");
    try {
      a.pop();
    } catch {
      return "";
    }
    return a.join("");
  });
}
