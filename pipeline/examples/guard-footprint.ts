// A type guard and an assertion function claim the footprint their bodies
// stay within, as a plain declaration does: a `map` callback calling them
// keeps its result dense.
export type Presence = "dense" | "readable" | "sparse";
function isPresence(value: unknown): value is Presence {
  return value === "dense" || value === "readable" || value === "sparse";
}
function presence(value: unknown): asserts value is Presence {
  if (!isPresence(value)) throw Error("expected a presence");
}
export function presences(vs: (string | number)[]): boolean[] {
  return vs.map((v) => isPresence(v));
}
export function checked(vs: (string | number)[]): Presence[] {
  return vs.map((v): Presence => {
    presence(v);
    return v;
  });
}
// A guard adding to a set it is given writes the set's internal slots, not a
// store: its footprint keeps every dense prefix, and `map` stays dense.
function isText(v: string | number, seen: Set<string>): v is string {
  if (typeof v !== "string") return false;
  seen.add(v);
  return true;
}
export function texts(vs: (string | number)[], seen: Set<string>): boolean[] {
  return vs.map((v) => isText(v, seen));
}
