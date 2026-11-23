type Handle = { xs: number[] };

export function sumVia(h: Handle): number {
  const xs = h.xs;
  let sum = 0;
  for (let i = 0; i < h.xs.length; i++) sum += xs[i]!;
  return sum;
}

export function sumViaKeepingFields(
  h: Handle,
  visit: () => Modifies<{ values: "keep"; spines: "grow" }, void>,
): number {
  const xs = h.xs;
  let sum = 0;
  for (let i = 0; i < h.xs.length; i++) {
    visit();
    sum += xs[i]!;
  }
  return sum;
}

export function sumViaDestructuring(h: Handle): number {
  const { xs } = h;
  let sum = 0;
  for (let i = 0; i < h.xs.length; i++) sum += xs[i]!;
  return sum;
}
