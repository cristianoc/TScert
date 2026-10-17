// A readonly view of `length` is met by an array as well as by a record, and
// an array's length is no field location: a test of it narrows no union of
// records, so the read of `a` after `o.length === 3` is refused, though
// TypeScript narrows it.
type Sized =
  | { readonly length: 3; readonly a: string }
  | { readonly length: 4; readonly b: number };

export function pick(o: Sized): string {
  return o.length === 3 ? o.a : String(o.b);
}
