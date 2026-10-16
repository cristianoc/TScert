// `Set<T>` and `Map<K, V>` are the library's interfaces through the reviewed
// overlay: their listed members, host-relative methods, with `add` and `set`
// returning the receiver; `new Set<T>(xs)` and `new Map<K, V>(es)` of arrays,
// or of nothing, at every element type. `get` may find no value.
function sets(): boolean {
  const s: Set<number> = new Set<number>([1, 2, 3]);
  s.add(4).add(5);
  const e = new Set<string>();
  e.delete("a");
  return s.has(1) && s.size > 0;
}

function maps(): number | undefined {
  const m = new Map<string, number>([["a", 1]]);
  m.set("b", 2).set("c", 3);
  const n: Map<string, boolean> = new Map();
  n.clear();
  return m.get("a");
}

function entries(
  es: readonly (readonly [string, number])[],
): Map<string, number> {
  return new Map(es);
}
