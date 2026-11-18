// A body that inserts at the front is within `spines: "grow"` but not
// `spines: "extend"`: every old element moves to the next index (run under
// Node: `const xs = [{ n: 1 }]; const a = xs[0]; front(xs); xs[0] === a` is
// `false`).
function front(xs: { n: number }[]): Modifies<{ values: "any"; spines: "extend" }, void> {
  xs.unshift({ n: 0 });
}

export function first(xs: { n: number }[]): number {
  front(xs);
  return xs.length;
}
