// A `flatMap` callback returning an empty array on one path and an array of
// strings on another: the binder of its elements is inferred from each
// return, so the result holds strings, which `join` converts.
const KEYS = ["Parts", "Lean"];

export function shown(m: Map<string, string>): string {
  const facts = KEYS.flatMap((k) => {
    const v = m.get(k);
    if (v === undefined) return [];
    return [`${k}=${v}`];
  });
  return facts.join(";");
}
