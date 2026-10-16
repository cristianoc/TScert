// A spread writes the elements of one array in place of several arguments. It
// is the last argument, so those elements are read after every other argument
// has been evaluated, which is where a call reads them. The operand is a name,
// so nothing is evaluated twice.
function spreadsPair(seed: boolean): boolean {
  const pair: [boolean, null] = [seed, null];
  const pick = (first: boolean, second: null): boolean => first;
  return pick(...pair);
}
function spreadsAfterFixed(seed: boolean): boolean {
  const pair: [boolean, boolean] = [seed, seed];
  const pick = (first: null, second: boolean, third: boolean): boolean => third;
  return pick(null, ...pair);
}
// Several spreads, or a spread before further arguments: each tuple's
// elements are read once every argument is evaluated, which is where the call
// reads them, since no argument after the first spread runs code.
function spreadsTwo(seed: boolean): boolean {
  const one: [boolean] = [seed];
  const two: [null, boolean] = [null, seed];
  const pick = (first: boolean, second: null, third: boolean): boolean => third;
  return pick(...one, ...two);
}
function spreadsBeforeFixed(seed: boolean): boolean {
  const pair: [boolean, null] = [seed, null];
  const pick = (first: boolean, second: null, third: boolean): boolean => third;
  return pick(...pair, seed);
}
// Into a generic signature, a spread's positions are actuals the binders are
// inferred from.
function both<T>(a: T, b: T): T {
  return b;
}
function spreadsGeneric(seed: boolean): boolean | null {
  const pair: [boolean, null] = [seed, null];
  return both(...pair);
}
