// `Map.prototype.{set, delete, clear}` and `Set.prototype.{add, delete, clear}`
// state the receiver-scoped frame `{this.size: scalar}`: they write only the
// receiver's internal slots (no location of the model) and its own `size` at
// `scalar` (SOURCE-CONTRACTS.md, "Native footprints"). Unrelated field
// narrowings and numeric field bounds survive each mutator by key disjointness,
// and functions calling them certify `Modifies<{ "m.size": "scalar" }, void>`
// and `Modifies<{ "s.size": "scalar" }, void>`.

type Cursor = { i: number; label: string | null };

/** @requires safeInteger(c.i) && 0 <= c.i && c.i < xs.length */
export function cursorAcrossMapMutators(
  m: Map<string, number>,
  c: Cursor,
  xs: number[],
): number {
  if (c.label !== null) {
    m.set("k", 1);
    m.delete("k");
    m.clear();
    return xs[c.i]! + c.label.length;
  }
  return 0;
}

/** @requires safeInteger(c.i) && 0 <= c.i && c.i < xs.length */
export function cursorAcrossSetMutators(
  s: Set<string>,
  c: Cursor,
  xs: number[],
): number {
  if (c.label !== null) {
    s.add("k");
    s.delete("k");
    s.clear();
    return xs[c.i]! + c.label.length;
  }
  return 0;
}

export function statedMapSize(
  m: Map<string, number>,
): Modifies<{ "m.size": "scalar" }, void> {
  m.set("a", 1);
  m.delete("a");
  m.clear();
}

export function statedSetSize(
  s: Set<string>,
): Modifies<{ "s.size": "scalar" }, void> {
  s.add("a");
  s.delete("a");
  s.clear();
}

/** @requires safeInteger(c.i) && 0 <= c.i && c.i < xs.length */
export function callerOfStatedMapSize(
  m: Map<string, number>,
  c: Cursor,
  xs: number[],
): number {
  statedMapSize(m);
  return xs[c.i]!;
}
