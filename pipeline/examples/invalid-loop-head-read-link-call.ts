// Calling a function whose effect may change fields (`values: "any"`) breaks
// the read link `xs ← h.xs` on the back edge, so the link is dropped at the
// loop head and `xs[i]!` is refused.
// Unsafe under Node: `sumViaCalls({ xs: [1] })` sets `h.xs = [1, 0]` on
// iteration 0 and reads `xs[1]` (`undefined`) on iteration 1, returning `NaN`.

function replaceWithLonger(h: {
  xs: number[];
}): Modifies<{ values: "any" }, void> {
  if (h.xs.length < 2) h.xs = [...h.xs, 0];
}

export function sumViaCalls(h: { xs: number[] }): number {
  const xs = h.xs;
  let s = 0;
  for (let i = 0; i < h.xs.length; i++) {
    replaceWithLonger(h);
    s += xs[i]!;
  }
  return s;
}
