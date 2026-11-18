// Standard library methods called on values from outside
// (docs/drafts/readonly-handles.md, "Storage no crossing reached"): a
// caller's handle holds a standard `Map`, whose `get` is the native method,
// and `Object.isFrozen` of a caller's record runs no code, no object being a
// proxy; neither calls its argument, so `read`'s frame runs no outside code
// and its push is admitted. `Array.prototype.map` calls its callback, here
// one calling the caller's, so `mapped`'s push is refused, though released
// arrays may come back through `walk`.
export type Handle = { readonly cache: Map<number, number> };

export function read(
  h: Handle,
  o: { items: string[] },
  n: number,
): { at: number }[] {
  const out: { at: number }[] = [];
  const k = h.cache.get(n);
  if (Object.isFrozen(o)) return out;
  out.push({ at: k ?? 0 });
  return out;
}

export function mapped(
  xs: readonly number[],
  f: (x: number) => Modifies<{ values: "any"; spines: "grow" }, number>,
): { at: number }[] {
  const res: { at: number }[] = [];
  const ys = xs.map((x) => f(x));
  res.push({ at: ys.length });
  return res;
}

export const walk = (h: unknown, visit: () => void): number => {
  visit();
  return h === undefined ? 0 : 1;
};
