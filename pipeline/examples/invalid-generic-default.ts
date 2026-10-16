// Calling only at boolean cannot justify a default that must work for every T.
function observedDefaultOnly(seed: boolean): boolean {
  const pick = <T>(value: T, flag: boolean = value): boolean => flag;
  return pick(seed, undefined);
}
