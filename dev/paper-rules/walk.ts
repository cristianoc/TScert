// The walk of "An effect language for TScert" (docs/drafts/effect-languages.md),
// for the paper-rules prototype (dev/paper-rules.mts). The ordinary reader
// reads `AtMost`'s argument and each instance as arguments without type
// meaning, and the visitor's `Modifies<E, void>` as changing every location.
type Footprint = { [location: string]: "keep" | "init" | "scalar" | "extend" | "grow" | "any" | true };
type AtMost<P extends Footprint> = Footprint;
type Visitor<E extends Footprint> = (i: number) => Modifies<E, void>;

export function walk<E extends AtMost<{ "xs[*]": "keep"; else: "any" }>>(xs: number[], visit: Visitor<E>): number {
  const c = { i: 0 };
  let sum = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i);
    sum += xs[c.i]!;
    c.i++;
  }
  return sum;
}

export function sumAndTrace(xs: number[]): number {
  const visited: number[] = [];
  return walk<{ "visited[*]": "extend" }>(xs, i => { visited.push(i); });
}

export function sumAndAlias(xs: number[]): number {
  const visited = xs;
  return walk<{ "visited[*]": "extend" }>(xs, i => { visited.push(i); });
}
