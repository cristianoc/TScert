// A method stating the empty footprint on normal return only: it calls a
// function typed `never`, which pops the array it is handed and throws, so
// the method meets its statement on every normal return, and its throw
// leaves the array shorter. A `map` callback catching that throw starts its
// handler in a heap the statement does not bound (run under Node: a hole).
export function die(xs: number[]): never {
  xs.pop();
  throw new Error("bumped");
}

export class Bump {
  bump(xs: number[]): Modifies<{}, number> {
    if (xs.length > 0) die(xs);
    return 0;
  }
}

export function wrong(b: Bump, xs: number[]): number[] {
  const r: number[] = xs.map((x) => {
    try {
      return b.bump(xs);
    } catch {
      return x;
    }
  });
  return r;
}

export function kept(b: Bump, xs: number[]): number[] {
  const r: number[] = xs.map(() => b.bump([]));
  return r;
}
