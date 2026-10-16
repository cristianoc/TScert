// A record parameter may own `__proto__`, which `Object.assign` would set
// through the prototype's setter, replacing the target's prototype: refused.
export function copy(p: { b: string }): { a: number; b: string } {
  return Object.assign({ a: 1 }, p);
}
