// A string set orders its elements by Unicode code point on the wire:
// U+E000, a private-use code point of the basic plane, before U+10000, a
// surrogate pair in UTF-16, whose code units would order it first.
export type Mark = "" | "\u{10000}" | "a";

export function width(m: Mark): number {
  if (m === "a") return 1;
  const rest: "" | "\u{10000}" = m;
  return rest.length;
}
