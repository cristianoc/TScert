// A generic closure whose signature spells its binder inside a type, a record
// `{ value: T }` or an array `readonly T[]`, called with its type argument
// inferred: the call's instance reads the binder as that argument inside the
// type too. A binder inferred from a type predicate the closure is passed, as
// TypeScript infers it. Census functions: `selectGlobal`
// (declaration-graph.mts, its `resolvedAmong`) and `makeProbe`
// (type-probe.mts, its `marked`).
interface Item {
  kind: "named" | "plain";
  pos: number;
}
interface Named extends Item {
  kind: "named";
  name: string;
}
interface Plain extends Item {
  kind: "plain";
}
type Entry = Named | Plain;

export function boxed(box: { value: number }): number {
  const read = <T>(b: { value: T }): T => b.value;
  return read(box);
}

export function among(items: readonly Named[], at: number): string {
  const resolvedAmong = <T extends Item>(
    candidates: readonly T[],
  ): T | undefined => candidates.find((m) => m.pos === at);
  const found = resolvedAmong(items);
  return found ? found.name : "";
}

export function marked(entry: Entry): string {
  const select = <N extends Entry>(
    test: (n: Entry) => n is N,
  ): N | undefined => (test(entry) ? entry : undefined);
  const found = select((n: Entry): n is Named => n.kind === "named");
  return found ? found.name : "";
}
