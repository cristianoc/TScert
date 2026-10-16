// A write at a key known only at run time through a dictionary the caller
// holds may add the key, which the caller would see: refused.
export function set(d: { [k: string]: number }, k: string): void {
  d[k] = 5;
}
