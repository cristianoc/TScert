// An indent, a primitive number or string, with a replacer that is `null`,
// absent or a list of keys, runs no code: `map`'s callback stays within the
// empty footprint and its result dense.
export function spaced(xs: number[]): string[] {
  return xs.map((x) => JSON.stringify(x, undefined, 2));
}

type Counts = { [k: string]: number };

export function tabbed(xs: readonly Counts[]): string[] {
  return xs.map((x) => JSON.stringify(x, null, "\t"));
}

export function picked(xs: readonly Counts[]): string[] {
  return xs.map((x) => JSON.stringify(x, ["a", 1], 1));
}
