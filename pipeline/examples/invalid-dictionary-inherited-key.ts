// An object literal inherits `Object.prototype`'s members: a read at a key
// known only at run time finds `toString` there, a function, where the
// dictionary's type says a number or nothing.
export function inherited(k: string): number {
  const d: { [k: string]: number } = {};
  return d[k] ?? 0;
}
