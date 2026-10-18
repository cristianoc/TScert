// TypeScript keeps a readonly optional key found present across a call of a
// method, which may run code deleting the key through another alias: the read
// after the call is read anew, of `string | undefined`.
interface Holder {
  readonly tag?: string;
  each<T>(f: (s: string) => T): T | undefined;
}

export function after(h: Holder): string {
  if (h.tag !== undefined) {
    h.each((s) => s.length);
    return h.tag;
  }
  return "";
}
