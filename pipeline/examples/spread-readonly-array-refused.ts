// A readonly array admits a node list, which is a host value: a spread of it
// is refused (R8, COMPILER-API.md).
export function copy(xs: readonly number[]): {} {
  return { ...xs };
}
