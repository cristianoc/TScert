// The twin of `invalid-guard-field-saved-callback`, at the same spans but the
// comparison's: its right side a literal, padded to the call's length.
// `pipeline/test.mts` gives this run's claims, at the call's spans, to the
// negative's document, that the producer refuses: the field's reread
// after the call is refused there.
type Box = { f: string | number };
export function wrong(x: Box, reset: Reset): number {
  if (x.f === "a"     ) return x.f.length;
  return 0;
}
type Reset = (x: Box) => "a";
