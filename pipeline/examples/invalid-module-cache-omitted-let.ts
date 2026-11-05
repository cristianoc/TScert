// A module `let` cache an omitted function returns (`--omit leak`, a
// census's omission): the cache is still no module's own object, and its
// key-adding write is refused (run under Node: a TypeError).
type K = "x" | "y";
let cache: Partial<Record<K, number>> = {};

function leak(): {} {
  return cache;
}
const alias: {} = leak();

function upper(o: { x?: string }): string {
  return o.x === undefined ? "" : o.x.toUpperCase();
}

export function run(key: K): string {
  cache[key] = 1;
  return upper(alias);
}

run("x");
