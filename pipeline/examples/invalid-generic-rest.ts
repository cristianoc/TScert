// Observed Boolean calls cannot justify an array of Boolean for arbitrary T.
function observedRestCallsOnly(flag: boolean, saved: boolean[]): boolean[] {
  const collect = <T>(...xs: T[]): T[] => saved;
  return collect(flag);
}
