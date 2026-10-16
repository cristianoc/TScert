// The same universally checked body collects independently typed fresh arrays.
function genericRestUses(flag: boolean, n: number): number[] {
  const collect = <T>(...xs: T[]): T[] => xs;
  const booleans = collect(flag, !flag);
  booleans[0] = flag;
  return collect(n, n);
}

// Declaration entry also certifies collection, not just an assumed array slot.
function genericRestDeclaration<T>(head: T, ...xs: T[]): T[] {
  const copy = xs;
  return copy;
}

// Fixed inputs precede the fresh rest binding; captures retain their types.
function genericRestPrefix(flag: boolean, n: number): number[] {
  const collect = <T>(first: T, ...xs: T[]): T[] => xs;
  const booleans = collect(flag);
  const pair: [number, number] = [n, n];
  return collect(n, ...pair);
}

// A default is checked universally before the rest body runs.
function genericDefaultRest(flag: boolean, n: number): number[] {
  const collect = <T>(seed: T, first: T = seed, ...xs: T[]): T[] => xs;
  const booleans = collect(flag);
  return collect(n, n, n);
}

// A possibly sparse spread contributes undefined to the inferred element type.
function genericRestSpread(
  input: (boolean | undefined)[],
): (boolean | undefined)[] {
  const collect = <T>(...xs: T[]): T[] => xs;
  return collect(...input);
}

// A variadic callback is callable inside a universal body at any finite arity.
function genericRestCallback<T>(emit: (...xs: T[]) => T[], value: T): T[] {
  return emit(value, value);
}

// The ordinary lowering shares the default/rest initialization schedule.
function ordinaryDefaultRest(seed: boolean): boolean[] {
  const collect = (first: boolean = seed, ...xs: boolean[]): boolean[] => xs;
  return collect(undefined, seed);
}
