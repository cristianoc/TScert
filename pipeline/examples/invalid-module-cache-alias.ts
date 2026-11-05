// A module constant bound to the cache holds its object too, at `{}`, which
// a parameter reads at `{ x?: string }`: the write adds `x` to the object
// both hold, and the reader calls a string method of a number (run under
// Node: a TypeError). The cache is no module's own object: its write is
// refused.
type Key = "x";
const cache: Partial<Record<Key, number>> = {};
const view: {} = cache;

function upper(o: { x?: string }): string {
  return o.x === undefined ? "" : o.x.toUpperCase();
}

export function run(key: Key): string {
  cache[key] = 1;
  return upper(view);
}

run("x");
