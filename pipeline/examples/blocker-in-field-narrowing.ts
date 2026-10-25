// A presence test on a union of records permitting extra properties cannot
// establish the tested property type: the other arm may own that key at
// another type.
// Census functions:
// fragment-guards.mts#guardOf, fragment-parse.mts#importedModules.
export function use(
  p: { guards: { value: number } } | { asserts: { value: number } },
): number {
  return "guards" in p ? p.guards.value : p.asserts.value;
}
