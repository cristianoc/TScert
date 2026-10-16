// A rest parameter collects the arguments after the fixed ones into a fresh
// array. Its contract is a tuple of required positions, which is exactly a
// fixed number of further arguments: the signature carries them, and the
// closure allocates the array where the parameter is bound, as the call does
// at run time.
function readsRest(first: boolean, ...rest: [boolean, boolean]): boolean {
  return rest[0];
}
function readsLaterElement(first: boolean, ...rest: [boolean, null]): null {
  return rest[1];
}
function collectsInClosure(seed: boolean): boolean {
  const pick = (first: boolean, ...rest: [boolean, boolean]): boolean => first;
  return pick(seed, seed, seed);
}
