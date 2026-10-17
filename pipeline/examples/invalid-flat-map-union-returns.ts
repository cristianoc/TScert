// A `flatMap` callback returning an empty array or an array of numbers: the
// elements are numbers, no strings.
const KEYS = ["Parts", "Lean"];

export function shown(m: Map<string, string>): string[] {
  return KEYS.flatMap((k) => {
    const v = m.get(k);
    if (v === undefined) return [];
    return [v.length];
  });
}
