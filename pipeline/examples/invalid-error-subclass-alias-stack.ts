// A write of `stack` through an alias typed without `Error`: JavaScript writes
// the instance's own non-enumerable `stack`, so a copy leaves it out (run under
// Node: `undefined`). Refused at the write.
class Decline extends Error {}
export function copied(): string {
  const o: { stack?: string } = new Decline("x");
  o.stack = "s";
  const copy: { stack: string } = { ...o };
  return copy.stack;
}
