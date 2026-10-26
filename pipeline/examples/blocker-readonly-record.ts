// Readonly over a record type, as the front end writes its tables: read
// through `Object.entries` and at its fields.
// Census functions: guard-closure.mts#guardClosure, array-prototype.mts#prototype,
// array-prototype.mts#mergeRefusal, host-families.mts#familyTable,
// family-activation.mts#checkedGuards, declaration-graph.mts#selectGlobal,
// fragment-parse.mts#lowerFile.
export function joined(files: Readonly<Record<string, string>>): string {
  let out = "";
  for (const [, text] of Object.entries(files)) out += text;
  return out;
}
export function total(t: Readonly<Record<"a" | "b", number>>): number {
  return t.a + t.b;
}
