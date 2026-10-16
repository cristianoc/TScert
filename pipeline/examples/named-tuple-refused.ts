// A tuple type with named members: the declaration reader lowers a tuple's
// element types and refuses member names it would otherwise drop.
type NamedPair = [flag: boolean, count: number];
export function first(pair: NamedPair): boolean {
  return pair[0];
}
