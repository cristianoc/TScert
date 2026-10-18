// A call between a field's equality test and its read may write the field:
// the test's fact is discarded, and the read is of the field's type
// (run under Node: the call stores "b", which `wrong` returns as "a").
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export function wrong(c: { kind: Json }, reset: () => void): "a" | null {
  let mode: "a" | null = null;
  if (c.kind === "a") {
    reset();
    mode = c.kind;
  }
  return mode;
}
