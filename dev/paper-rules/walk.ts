// The walk of "An effect language for TScert" (docs/drafts/effect-languages.md),
// for the paper-rules prototype (dev/paper-rules.mts). `AtMost` is a local
// alias, so the ordinary reader sees a plain bound; each effect is written as a
// string literal type holding the paper's literal, since the ordinary reader
// refuses an object type with keys such as "xs[*]" in a type argument.
type AtMost<P> = unknown;
type Visitor<E> = (i: number) => void;

export function walk<E extends AtMost<'{ "xs[*]": "keep", "else": "any" }'>>(xs: number[], visit: Visitor<E>): number {
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
  return walk<'{ "visited[*]": "extend" }'>(xs, i => { visited.push(i); });
}

export function sumAndAlias(xs: number[]): number {
  const visited = xs;
  return walk<'{ "visited[*]": "extend" }'>(xs, i => { visited.push(i); });
}
