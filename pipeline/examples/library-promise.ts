// The standard library's Promise, read from its merged declarations: a value
// passes through at that type.
export function same(p: Promise<number>): Promise<number> {
  return p;
}
