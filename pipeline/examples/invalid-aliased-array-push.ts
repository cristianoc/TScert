// Pushing onto a parameter array `out` not known apart from `p.widths` does not
// preserve `p.flags.length === p.widths.length`: refused. Under Node, calling
// `appendInto(p, p.widths)` with `flags: new Uint8Array(1), widths: [1]` grows
// `p.widths` to length 2 while `p.flags.length` stays 1.
/** @invariant this.flags.length === this.widths.length */
type Base = { flags: Uint8Array; widths: number[] };

export function appendInto(p: Base, out: number[]): Base {
  /** @invariant p.flags.length === p.widths.length && p.widths !== out */
  for (let i = 0; i < p.flags.length; i++) {
    out.push(p.flags[i]!);
  }
  return p;
}
