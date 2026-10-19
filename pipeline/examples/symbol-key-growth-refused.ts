// A key-adding write at a fresh symbol a function returns at `symbol`: the
// key may be any symbol, `Symbol.toStringTag` among them, which no object the
// program makes may hold, so the write is refused, though this key never is
// the tag.
function fresh(): symbol {
  return Symbol("k");
}

export function marked(): { [k: symbol]: number } {
  const d: { [k: symbol]: number } = {};
  d[fresh()] = 1;
  return d;
}
