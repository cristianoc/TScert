// A call between the test of a dictionary's entry and its read may write
// the entry: the test's fact is discarded, and the read is of what the
// index holds or `undefined` (run under Node: `wrong({ mapping: [] }, ...)`
// returns the string the call stored).
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
type Target = { [key: string]: Json };
export function wrong(t: Target, reset: () => void): Json[] {
  if (!Array.isArray(t.mapping)) return [];
  reset();
  return t.mapping;
}
