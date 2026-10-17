// A callback popping a fresh array inside `try`: the result is dense, but a
// handler could resume after mutation the bound does not track, so the
// node-by-node bound refuses any node with one and `map` takes its signature
// with holes: a gap.
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
