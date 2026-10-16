// Closures that collect a rest, take a default, are generic, construct an
// instance or initialize a callable object are graph code as any other: a
// rest's store, a default and the parameters are bound at the code's entry,
// and loops, `switch`, `try` and mutable locals run inside.
function sumRest(seed: number): number {
  const sum = (first: number, ...rest: number[]): number => {
    let total = first;
    for (const x of rest) total += x;
    return total;
  };
  return sum(seed, 1, 2) + sum(seed);
}
function tupleRest(seed: number): number {
  const pick = (...pair: [number, string]): number => {
    let result = 0;
    switch (pair[1]) {
      case "a":
        result = pair[0];
        break;
      default:
        result = 1;
    }
    return result;
  };
  return pick(seed, "a");
}
function defaulted(seed: number): number {
  const scale = (x: number, by: number = 2): number => x * by;
  const later = (
    x: number,
    read: () => number = (): number => y,
    y: number = x,
  ): number => read();
  return scale(seed) + scale(seed, 3) + later(seed);
}
function genericRest(seed: boolean): number {
  const count = <T>(...xs: T[]): number => {
    let n = 0;
    while (n < xs.length) n += 1;
    return n;
  };
  return count(seed, !seed);
}
function genericDefault(seed: string): string {
  const first = <T>(value: T, fallback: T = value): T => {
    try {
      return fallback;
    } catch {
      return value;
    }
  };
  return first(seed);
}
class Accumulator {
  total: number;
  constructor(values: number[]) {
    let total = 0;
    for (const v of values) total += v;
    this.total = total;
  }
}
function callable(seed: number): number {
  const f = Object.assign<(...xs: number[]) => number, { base: number }>(
    (...xs: number[]): number => {
      let n = 0;
      for (const x of xs) n += x;
      return n;
    },
    { base: seed },
  );
  return f(f.base, 1) + new Accumulator([seed, 2]).total;
}
