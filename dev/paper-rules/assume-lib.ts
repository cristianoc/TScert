// A module holding an unsafe assume, imported by assume-importer.ts.

// `paperAssume(fact, "#N");` is the prototype's unsafe assume.
function paperAssume(fact: boolean, issue: string): Modifies<{}, void> {}

// Accepted by the prototype, naming #356; refused by the ordinary verifier.
export function first(xs: number[], opaque: () => void): number {
  opaque();
  paperAssume(xs.length > 0, "#356"); // unsafe assume
  return xs[0]!;
}

// Accepted.
export function size(xs: number[]): number {
  return xs.length;
}
