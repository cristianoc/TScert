// The field's value the comparison tests is the one read before the call; the
// call writes the field, so the reread after it is of a number, of which
// `length` is `undefined` (run under Node).
function reset(x: { f: string | number }): "a" {
  x.f = 0;
  return "a";
}
export function wrong(x: { f: string | number }): number {
  if (x.f === reset(x)) return x.f.length;
  return 0;
}
