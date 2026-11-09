// An arrow popping the mapped array, passed where a function type stating
// the empty footprint is expected: the argument's contract compares effects,
// and the arrow's states none (run under Node: a hole).
export function mapped(
  xs: number[],
  f: (x: number) => Modifies<{}, number>,
): number[] {
  const r: number[] = xs.map((x) => f(x));
  return r;
}

export function wrong(xs: number[]): number[] {
  return mapped(xs, (x: number): number => {
    xs.pop();
    return x;
  });
}
