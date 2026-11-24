// Object spread `{ ...p, extra }` preserves read links and field-rooted index
// facts on every non-overridden key of `p`.
/** @invariant this.flags.length === this.widths.length */
type Base = { flags: Uint8Array; widths: number[] };
type Extended = Base & { extra: number };

export function extend(p: Base, extra: number): Extended {
  const result = { ...p, extra };
  return result;
}
