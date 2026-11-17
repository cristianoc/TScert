// `x / 2` returned at `SafeInt`: no fact states the quotient a safe integer,
// so the return is refused. Under Node `middle([10, 20], 3)` reads
// `xs[1.5]`, `undefined` at `number`.

export function half(x: SafeInt): SafeInt {
  return x / 2;
}

/** @requires 0 <= i && i < xs.length */
function at(xs: number[], i: SafeInt): number {
  return xs[i]!;
}

export function middle(xs: number[], n: SafeInt): number {
  const i = half(n);
  if (0 <= i && i < xs.length) return at(xs, i);
  return 0;
}
