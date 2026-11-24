// A call may change a captured cell's contents: TypeScript keeps
// `refused` narrowed to `false` across the calls of the literal that
// assigns it, so `closed` returns `true` at its declared result `false`
// (run under Node: `closed(["x"])` returns true).
export function closed(xs: string[]): false {
  let refused = false;
  const visit = (s: string): void => {
    if (s === "x") refused = true;
  };
  for (const x of xs) visit(x);
  return refused;
}
