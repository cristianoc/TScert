// `Pick` at a named type with a field of function type, as the regexp
// reader's `Pick<RegExpKeys, "stringIterator" | "iterator">`: the picked
// fields at the types the alias declares them (rule mapped-pick).
type Keys = {
  match: number;
  stringIterator: number;
  iterator: (element: string) => string;
};

export function iterate(
  keys: Pick<Keys, "stringIterator" | "iterator">,
): string {
  return keys.iterator(String(keys.stringIterator));
}
export function choose(keys: Keys): Pick<Keys, "match"> {
  return keys;
}
