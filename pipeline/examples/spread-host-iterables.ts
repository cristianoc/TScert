// An argument spread of a host iterable other than an array collects what
// its iterator yields into a fresh array, `%Spread:K%`, spread where it is
// written: a `Set`'s elements, a `Map` iterator's values among other
// arguments, a string's code points.
function sum(...xs: number[]): number {
  let n = 0;
  for (const x of xs) n += x;
  return n;
}

export function spreadSet(s: Set<number>): number {
  return sum(...s);
}

export function spreadValues(m: Map<string, number>): number {
  return sum(1, ...m.values(), 2);
}

function count(...parts: string[]): number {
  return parts.length;
}

export function spreadString(s: string): number {
  return count(...s);
}
