// The closure's parameter is an Iterator<number>, whose defaulted arguments
// TypeScript instantiates at `any`: Iterator<number, any, any> states no
// contract for its result and argument, so the parameter is refused.
export function firsts(its: readonly Iterator<number>[]): number {
  let n = 0;
  its.forEach((it) => {
    const r = it.next();
    if (!r.done) n += r.value;
  });
  return n;
}
