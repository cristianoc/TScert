// A `typeof` test of a value whose type is a named union decides the arms
// of its definition: where `typeof k === "string"` fails, a `Key` is its
// record, in a module constant's arrow as in a function declaration.
type Key = string | { symbol: number };
export const showKey = (k: Key): string =>
  typeof k === "string" ? k : `sym#${k.symbol}`;
export const symbolOf = (k: Key): number => {
  if (typeof k === "string") return -1;
  return k.symbol;
};
