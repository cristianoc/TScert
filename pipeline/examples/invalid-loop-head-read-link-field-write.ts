type Handle = { xs: number[] };

export function sumViaReplacingField(h: Handle): number {
  const xs = h.xs;
  let sum = 0;
  for (let i = 0; i < h.xs.length; i++) {
    sum += xs[i]!;
    if (i === 0) h.xs = [1, 2];
  }
  return sum;
}
