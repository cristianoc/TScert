// Census functions:
// fragment-parse.mts#parseFile
// fragment-parse.mts#parseFragment
// fragment-parse.mts#lowerModule
// fragment-parse.mts#lowerModuleText
// fragment-parse.mts#parseModules
// fragment-parse.mts#lowerFile
export function lower(
  input: number[],
  make: (n: number) => string,
  keep: (n: number) => boolean,
): string[] {
  let lowered = input.map((s) => ({ s, fn: make(s) }));
  for (let changed = true; changed; ) {
    const kept = lowered.filter(({ s }) => keep(s));
    changed = kept.length < lowered.length;
    lowered = kept;
  }
  return lowered.map(({ fn }) => fn);
}
