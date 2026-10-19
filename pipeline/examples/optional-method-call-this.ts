// `o.m?.()` tests the method and calls it with `o` as its receiver, read
// again: a field whose function states its receiver.
interface Maybe {
  m?: (this: Maybe) => number;
}
export function call(o: Maybe): number | undefined {
  return o.m?.();
}
