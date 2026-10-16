// A declaration may hide a module value of its name: the name is the
// declaration's in the rest of its block, and the module's again after it.
const seed: number = 1;
function hidesInBlock(flag: boolean): number {
  if (flag) {
    const seed: string = "local";
    return seed.length;
  }
  return seed;
}
function hidesInBody(): string {
  const seed: string = "local";
  const read = (): string => seed;
  return read();
}
function readsBeforeBlock(): number {
  if (seed === 1) {
    const seed = 2;
    return seed;
  }
  return 0;
}
function hidesAsCell(): number {
  let seed = 2;
  seed = seed + 1;
  return seed;
}
const later: number = 1;
function patternEarlier(source: { first?: number; later?: number }): number {
  const { later = 2, first = later } = source;
  return first;
}
