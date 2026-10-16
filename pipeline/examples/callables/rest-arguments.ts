function collectsRest(first: boolean, ...rest: [boolean, boolean]): boolean {
  return rest[0];
}
function readsLaterElement(first: boolean, ...rest: [boolean, null]): null {
  return rest[1];
}
function spreadsPair(seed: boolean): boolean {
  const pair: [boolean, boolean] = [seed, seed];
  const pick = (first: boolean, second: boolean): boolean => second;
  return pick(...pair);
}
function spreadsAfterFixed(seed: boolean): boolean {
  const pair: [boolean, null] = [seed, null];
  const pick = (first: null, second: boolean, third: null): boolean => second;
  return pick(null, ...pair);
}
