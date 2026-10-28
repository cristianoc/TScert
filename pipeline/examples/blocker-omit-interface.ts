// Omit of an interface needs the library's Omit read at its instance, where
// keyof of the interface is a union of literals.
// Census functions:
// declaration-graph.mts#selectGlobal, library-modules.mts#moduleEntries.
interface Entry {
  stated: number;
  name: string;
}
export function rest(e: Entry): Omit<Entry, "stated"> {
  return { name: e.name };
}
