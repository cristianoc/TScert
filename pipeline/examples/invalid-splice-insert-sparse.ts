// Splice preserves holes in its removed range; insertion does not fill them.
export function broken(xs: string[]): string {
  const sparse = xs.map((x) => {
    xs.pop();
    return x;
  });
  const removed = sparse.splice(0, 3, "replacement");
  let result = "";
  for (const value of removed) result += value.toUpperCase();
  return result;
}
