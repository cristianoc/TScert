// An array rest collects any number of arguments into one fresh array. A
// spread passes an array's elements among them, read where it is written.
function collects(first: boolean, ...rest: boolean[]): boolean[] {
  return rest;
}
function spreadsAmongActuals(seed: boolean): (boolean | undefined)[] {
  const values: boolean[] = [seed, seed];
  const collect = (...rest: (boolean | undefined)[]): (boolean | undefined)[] =>
    rest;
  return collect(seed, ...values, seed);
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
function variadicCallableField(seed: boolean): boolean[] {
  const f = Object.assign<
    (...rest: boolean[]) => boolean[],
    { value: boolean }
  >((...rest: boolean[]): boolean[] => rest, { value: seed });
  f.value = !seed;
  return f(f.value, seed);
}
function readsBeforeLaterWrite(seed: boolean): (boolean | undefined)[] {
  const values: boolean[] = [seed];
  const collect = (...rest: (boolean | undefined)[]): (boolean | undefined)[] =>
    rest;
  return collect(...values, (values[0] = !seed));
}
