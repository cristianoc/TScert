// A `let` whose bindings nothing assigns is a `const`: each holds its initial
// value throughout. So a tag test narrows it, and a pattern binds it.
type U = { kind: "a"; name: string } | { kind: "b"; n: number };

export function narrowed(p: U): string {
  let u = p;
  if (u.kind === "a") {
    return u.name;
  }
  return String(u.n);
}

export function pattern(pair: readonly [number, string]): number {
  let [n, s] = pair;
  return n + s.length;
}
