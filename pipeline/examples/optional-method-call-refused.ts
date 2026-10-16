// `o.m?.()` tests the method but calls it with `o` as its receiver, which the
// chain does not save apart from the tested value: refused.
interface Maybe {
  m?: (this: Maybe) => number;
}
function call(o: Maybe): number | undefined {
  return o.m?.();
}
