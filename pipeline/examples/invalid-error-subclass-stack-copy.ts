// A write of `stack` onto an instance keeps JavaScript's own property
// non-enumerable, so a copy leaves it out (run under Node: `undefined`),
// where the model would add an enumerable own key. Refused at the write.
class Decline extends Error {}
export function copied(): string {
  const e = new Decline("x");
  e.stack = "s";
  const copy: { stack: string } = { ...e };
  return copy.stack;
}
