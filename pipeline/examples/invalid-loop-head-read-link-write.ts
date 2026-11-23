// Writing `h.xs` inside the loop breaks the read link `xs ← h.xs` on the back
// edge, so the link is dropped at the loop head and `xs[i]!` is refused.
// Unsafe under Node: `sumViaWrites({ xs: [1] })` sets `h.xs = [1, 0]` on
// iteration 0 and reads `xs[1]` (`undefined`) on iteration 1.

export function sumViaWrites(h: { xs: number[] }): number {
  const xs = h.xs;
  let s = 0;
  for (let i = 0; i < h.xs.length; i++) {
    h.xs = [...xs, 0];
    s += xs[i]!;
  }
  return s;
}
