// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// the initialization of prepare.ts and line-breaks.ts (no function refused
// on its own).
// Refusal: gate: the method String.raw is only called, on its host.
// `String.raw` as a template tag in the initialization: the method is
// admitted only when called on its host. In pretext it refuses the
// initialization of `prepare.ts` and `line-breaks.ts`, which blocks their
// functions' deep status.
const pattern: string = String.raw`[ぁ-ヿ]`;
export function source(): string {
  return pattern;
}
