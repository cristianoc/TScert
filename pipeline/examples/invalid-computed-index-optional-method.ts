// An optional method read through an indexed access keeps its receiver:
// a Big's record may read `this.extra`, which a Scope does not have, so it is
// no function Scope["record"] states (TypeScript accepts the return).
type Scope = { size: number; record?(key: string): number };
type Big = { size: number; extra: string; record?(key: string): number };

export function widen(b: Big): Scope["record"] {
  return b.record;
}
