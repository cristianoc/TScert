// A reference omitting a type argument whose default is `Partial` of a named
// interface: the declaration graph completes the argument while it collects
// the definitions, and it is expanded once they are complete (rule
// mapped-identity).
interface Context {
  a: number;
  b: string;
}
interface Holder<T = Partial<Context>> {
  value: T;
}
export function read(h: Holder): number {
  return h.value.a ?? 0;
}
