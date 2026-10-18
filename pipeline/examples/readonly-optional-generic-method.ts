// A test finding a readonly optional key present keeps the object's declared
// shape: its generic method stays a method, called after the test, and the
// key's read is the value the test found.
interface Holder {
  readonly tag?: string;
  each<T>(f: (s: string) => T): T | undefined;
}

export function collect(h: Holder, out: string[]): number | undefined {
  if (h.tag !== undefined) {
    out.push(h.tag);
    return h.each((s) => s.length);
  }
  return undefined;
}
