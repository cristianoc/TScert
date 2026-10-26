// A mapped type at a named type with a method: the method's receiver is the
// interface, of which the mapped field is no member, and the reader refuses it.
interface Reader {
  read(): number;
}
export function read(r: Readonly<Reader>): number {
  return r.read();
}
