// A call between the test and the read may write the field: the test's fact
// is discarded, and the read is of the field's type.
type Box = { mapping: number[] | number };
export function wrong(t: Box, reset: () => void): number[] {
  if (!Array.isArray(t.mapping)) return [];
  reset();
  return t.mapping;
}
