// A memoizing lifter of JSON rows in the forms claim-text.mts writes it: each
// function states that it only grows the store, so `map` over a dense
// receiver keeps its result dense; the first, possibly absent, row is lifted
// apart from the rest, a JSON array whose elements are never absent; the
// lifted record states its index signature; the table's names are a native
// `Map`; a closure captures a tested name through a constant of the tested
// type.
// Census functions:
// claim-text.mts#liftClause
// claim-text.mts#liftSignatures
// claim-text.mts#liftType
// claim-text.mts#liftLabels
// claim-text.mts#treeAtom
// claim-text.mts#lift
type JsonValue =
  | null
  | boolean
  | number
  | string
  | readonly JsonValue[]
  | { readonly [key: string]: JsonValue };
type Shown = {
  readonly [key: string]: JsonValue;
  top: boolean;
  atoms: JsonValue[];
};
interface Table {
  names: Map<number, string>;
  lifted: Map<string, Shown>;
}
const shown = (
  table: Table,
  row: JsonValue | undefined,
): Modifies<{ values: "any"; stores: "grow" }, Shown> => {
  const key = row === undefined ? "undefined" : JSON.stringify(row);
  const held = table.lifted.get(key);
  if (held !== undefined) return held;
  const name = typeof row === "number" ? table.names.get(row) : undefined;
  let atoms: JsonValue[] = [typeof row];
  if (name !== undefined) {
    const named: string = name;
    const later = (): Modifies<
      { values: "any"; stores: "grow" },
      JsonValue[]
    > => [named];
    atoms = later();
  }
  const lifted: Shown = { top: false, atoms };
  table.lifted.set(key, lifted);
  return lifted;
};
export function liftAll(
  table: Table,
  first: JsonValue | undefined,
  rest: readonly JsonValue[],
): JsonValue {
  const later = (
    row: JsonValue,
  ): Modifies<{ values: "any"; stores: "grow" }, Shown> => shown(table, row);
  const cells = [shown(table, first), ...rest.map(later)];
  const [only] = cells;
  if (only === undefined || cells.length !== 1) return cells;
  return only;
}
