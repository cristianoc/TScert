// An interface whose call signature is generic: the declaration reader lowers
// a call signature's parameters and result, and refuses one that binds its own
// type parameters.
interface GenericCall {
  <T>(value: T): T;
}
export function apply(f: GenericCall): number {
  return f(1);
}
