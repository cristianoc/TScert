// A symbol index signature constrains every symbol key, and no string key:
// the two key spaces are disjoint.
const tag: unique symbol = Symbol("tag");
type Tags = { readonly [k: symbol]: boolean };
type Both = { readonly [k: string]: number; readonly [k: symbol]: boolean };

function dynamic(t: Tags, s: symbol): boolean | undefined {
  return t[s];
}
// A `unique symbol` key is one symbol key.
function tagged(t: Tags): boolean | undefined {
  return t[tag];
}
function both(b: Both, s: symbol, k: "a" | "b"): boolean | number | undefined {
  return b[s] ?? b[k];
}
// A named symbol-keyed member reads at its own contract.
function marked(t: {
  readonly [tag]: number;
  readonly [k: symbol]: boolean;
}): number {
  return t[tag];
}
function forget(b: Both): Tags {
  return b;
}
export function use(
  s: symbol,
  m: { readonly [tag]: number; readonly [k: symbol]: boolean },
): number {
  const t: Tags = {};
  const b: Both = { a: 1 };
  const seen = dynamic(t, s) ?? tagged(t) ?? forget(b)[s] ?? false;
  const read = both(b, s, "a") ?? 0;
  return (seen ? 1 : 0) + (read === true ? 1 : 0) + marked(m);
}
