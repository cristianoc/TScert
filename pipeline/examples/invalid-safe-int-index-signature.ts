// An index signature keyed by `SafeInt`: TypeScript reads its key at
// `number`, which would widen the keys it states to every number, so the
// form is refused at the source boundary.
export function get(r: { [k: SafeInt]: string }, k: number): string | undefined {
  return r[k];
}
