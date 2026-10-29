// Omit of an interface or an object type alias is the library's
// `Pick<T, Exclude<keyof T, K>>` at its arguments: the kept members, each
// with its modifiers, readonly and optional ones among them.
// Census functions:
// declaration-graph.mts#collectDeclarations, declaration-graph.mts#selectGlobal,
// library-modules.mts#moduleObjectDefault, library-modules.mts#moduleEntries.
interface Entry {
  stated: number;
  name: string;
  readonly kind: "a" | "b";
  note?: string;
}
type Row = { binding: string; size: number };
export function rest(e: Entry): Omit<Entry, "stated"> {
  return { name: e.name, kind: e.kind };
}
export function width(e: Omit<Entry, "stated" | "note">): number {
  return e.name.length + (e.kind === "a" ? 1 : 2);
}
export function noted(e: Omit<Entry, "stated">): string {
  return e.note ?? e.name;
}
export function sized(r: Omit<Row, "binding"> & { extra?: number }): number {
  return r.size + (r.extra ?? 0);
}
