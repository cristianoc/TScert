// An array pattern whose positional reads are its iterator's steps: over a
// fresh array literal, which no other reference reaches, any code may run
// between the steps; over an array another reference may hold, the code run
// between them changes no array: defaults that only read, and writes at named
// fields.
export function freshSource(box: { slot: number }, log: { n: number }): number {
  [, box[(log.n = log.n + 1) === 0 ? "slot" : "slot"] = 9] = [0, undefined];
  return box.slot + log.n;
}

export function heldSource(
  xs: number[],
  box: { first: number; second: number },
): number {
  let a: number | undefined = 0;
  [a, box.first = 2, , box.second = 3] = xs;
  return (a ?? 1) + box.first + box.second;
}

export function boundDefaults(xs: number[]): number {
  const [a = 1, , b = a, ...rest] = xs;
  return a + b + rest.length;
}
