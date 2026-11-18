// A frame that reads the module's own `WeakMap` at a key from outside and
// pushes records into an array it allocated: `WeakMap.prototype.get` calls no
// argument its declaration types by a type parameter, so the frame runs no
// outside code, and (O) admits the push, though released arrays may come
// back read-only through `walk`.
const cache = new WeakMap<object, number>();

export function measure(h: object, n: number): { at: number }[] {
  const out: { at: number }[] = [];
  const known = cache.get(h);
  for (let i = 0; i < n; i++) out.push({ at: known ?? i });
  return out;
}

export const walk = (h: unknown, visit: () => void): number => {
  visit();
  return h === undefined ? 0 : 1;
};
