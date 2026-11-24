// A freshly allocated array literal `const kinds: number[] = []` has a spine
// apart from existing field-rooted array paths named in the state's index facts
// (`p.widths !== kinds`), preserving `p.flags.length === p.widths.length`
// across a loop that pushes to `kinds` and into an object spread `{ ...p, kinds }`.
/** @invariant this.flags.length === this.widths.length */
type Base = { flags: Uint8Array; widths: number[] };
type WithKinds = Base & { kinds: number[] };

export function attachKinds(p: Base): WithKinds {
  const kinds: number[] = [];
  /** @invariant p.flags.length === p.widths.length && p.widths !== kinds */
  for (let i = 0; i < p.flags.length; i++) {
    kinds.push(p.flags[i]!);
  }
  const result = { ...p, kinds };
  return result;
}
