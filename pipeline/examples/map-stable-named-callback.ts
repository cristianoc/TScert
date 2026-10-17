// A module constant passed by name as a `map` callback: it takes one
// parameter where `map` passes three, and replaces through a global regex,
// within `{value: any, store: keep}`, so `map` takes that footprint's dense
// signature and the result is dense.
const escaped = (s: string): string => s.replace(/&/g, "&amp;");

export function escapedAll(xs: string[]): string {
  return xs.map(escaped).join(",");
}
