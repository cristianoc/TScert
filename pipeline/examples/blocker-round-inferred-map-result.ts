// Census: declaration-graph.mts#selectGlobal, forms(overload, key, what, entry).
// A resolved overlay has array forms; the helper consumes only its effect.
type Entry = { effect?: number; forms?: number[] | (() => number[]) };
type Resolved = Omit<Entry, "forms"> & { forms?: number[] };
type Form = { receiver: string | null; effect: number };
export function select(xs: Form[], entry: Resolved): Form[] {
  const forms = (entry: Pick<Entry, "effect">) =>
    xs.map((form) => ({ ...form, effect: entry.effect ?? form.effect }));
  return forms(entry).map((form) => ({ ...form, receiver: "self" }));
}
