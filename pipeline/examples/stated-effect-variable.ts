// A callback whose effect is a type parameter, `Modifies<E, void>`: the
// walker reads it as changing every location, so it reads `xs` again after
// each call, and the caller's instance, an object type, is not lowered
// (SOURCE-ELABORATION.md, "Stated effects").
type Footprint = { [location: string]: "keep" | "init" | "scalar" | "extend" | "grow" | "any" };
type AtMost<P extends Footprint> = Footprint;
type Visitor<E extends Footprint> = (i: number) => Modifies<E, void>;

export function walk<E extends AtMost<{ "xs[*]": "keep"; else: "any" }>>(xs: number[], visit: Visitor<E>): number {
  let sum = 0;
  for (let i = 0; i < xs.length; i++) {
    visit(i);
    if (i < xs.length) sum += xs[i]!;
  }
  return sum;
}

export function walkInline<E extends Footprint>(xs: number[], visit: (i: number) => Modifies<E, void>): void {
  for (let i = 0; i < xs.length; i++) visit(i);
}

export function trace(xs: number[]): number[] {
  const visited: number[] = [];
  walk<{ "visited[*]": "extend" }>(xs, i => { visited.push(i); });
  walkInline<{ "visited[*]": "extend" }>(xs, i => { visited.push(i); });
  return visited;
}
