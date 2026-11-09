// A location key at `true`, which the index signature admits for
// `onThrow`: a location's change is a change or a class map.
let cache: number | null = null;

export function cached(): Modifies<{ "cell(cache)": true }, number> {
  cache ??= 1;
  return cache;
}
