// A property key of an object pattern spelled as a later local needs to be
// read as a key: it reads no binding.
// Census functions:
// declaration-graph.mts#selectGlobal.
export function size(entry: { stated: number; name: string }): number {
  const { stated: written, ...rest } = entry;
  const stated = written + rest.name.length;
  return stated;
}
