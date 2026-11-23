// A callback whose effect is a type parameter, `Modifies<E, void>`, may
// change every location, whatever bound `E` has: the walker keeps no fact
// about `xs` across the call, and its read `xs[i]!` is refused. Under Node,
// `lastVisited<{ "shrink[*]": "any" }>(shrink, () => { shrink.pop(); })`
// with `shrink` `[1, 2, 3]` returns `undefined` at `number`.
type Footprint = { [location: string]: "keep" | "init" | "scalar" | "extend" | "grow" | "any" };
type AtMost<P extends Footprint> = Footprint;
type Visitor<E extends Footprint> = (i: number) => Modifies<E, void>;

export function lastVisited<E extends AtMost<{ "xs[*]": "keep"; else: "any" }>>(xs: number[], visit: Visitor<E>): number {
  if (xs.length === 0) return 0;
  const i = xs.length - 1;
  visit(i);
  return xs[i]!;
}

export function popped(): number {
  const shrink = [1, 2, 3];
  return lastVisited<{ "shrink[*]": "any" }>(shrink, () => { shrink.pop(); });
}
