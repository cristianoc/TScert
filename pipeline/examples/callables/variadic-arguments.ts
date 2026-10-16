function returnsRest(seed: boolean, ...flags: boolean[]): boolean[] {
  return flags;
}
function callsCollector(seed: boolean): boolean[] {
  const collect = (first: boolean, ...rest: boolean[]): boolean[] => rest;
  return collect(seed, seed, !seed);
}
function spreadsIntoRest(seed: boolean): (boolean | undefined)[] {
  const values: boolean[] = [seed, seed];
  const collect = (
    first: boolean,
    ...rest: (boolean | undefined)[]
  ): (boolean | undefined)[] => rest;
  return collect(seed, ...values, seed, ...values);
}
function spreadsTupleIntoRest(seed: boolean): boolean[] {
  const pair: [boolean, boolean] = [seed, seed];
  const collect = (...rest: boolean[]): boolean[] => rest;
  return collect(...pair);
}
function passesCollectorOn(seed: boolean): boolean {
  const collect = (first: boolean, ...rest: boolean[]): boolean => first;
  const apply = (f: (first: boolean, ...rest: boolean[]) => boolean): boolean =>
    f(seed, seed);
  return apply(collect);
}
function variadicAsFixed(seed: boolean): boolean[] {
  const collect = (...rest: boolean[]): boolean[] => rest;
  const apply = (f: (x: boolean) => boolean[]): boolean[] => f(seed);
  return apply(collect);
}
function omitsBeforeRest(seed: boolean): boolean | undefined {
  const first = (x?: boolean, ...rest: boolean[]): boolean | undefined => x;
  return first();
}
function mixedSignatures(seed: boolean): boolean[] {
  const collect: ((x: boolean) => boolean[]) &
    ((...rest: boolean[]) => boolean[]) = (...rest: boolean[]): boolean[] =>
    rest;
  const one = collect(seed);
  return collect(seed, seed);
}
function variadicCallableField(seed: boolean): boolean[] {
  const f = Object.assign<
    (...rest: boolean[]) => boolean[],
    { value: boolean }
  >((...rest: boolean[]): boolean[] => rest, { value: seed });
  f.value = !seed;
  return f(f.value, seed);
}
