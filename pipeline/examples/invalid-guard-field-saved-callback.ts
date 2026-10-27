// The field's value the comparison tests is the one read before the call; the
// callback may write the field, so the reread after it is of a number, of
// which `length` is `undefined` (run under Node). The producer refuses it;
// `pipeline/test.mts` checks it with its twin's claims
// (`guard-field-saved-twin-prettier-ignore`).
type Box = { f: string | number };
export function wrong(x: Box, reset: Reset): number {
  if (x.f === reset(x)) return x.f.length;
  return 0;
}
type Reset = (x: Box) => "a";
