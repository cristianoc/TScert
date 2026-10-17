// A call whose signature bounds the heap its throw leaves, as its footprint
// bounds a normal return's, may be caught: the handler starts in a heap the
// footprint relates to the call's entry, so a callback catching it keeps
// `map`'s result dense. The callees build an error and throw it, which
// writes nothing they did not allocate, so each states the empty footprint
// on a throw; a handler rethrowing keeps it, and a constant's arrow states it
// as a declaration does.
function checked(x: number): number {
  if (x < 0) throw Error(`negative: ${x}`);
  return x;
}
const halved = (x: number): number => {
  if (x % 2 !== 0) throw Error(`odd: ${x}`);
  return x / 2;
};
function relayed(x: number): number {
  try {
    return checked(x);
  } catch (e) {
    throw e;
  }
}
export function orZero(xs: number[]): number[] {
  return xs.map((x: number): number => {
    try {
      return checked(x);
    } catch {
      return 0;
    }
  });
}
export function halvesOrSelf(xs: number[]): number[] {
  return xs.map((x: number): number => {
    try {
      return halved(x);
    } catch {
      return x;
    }
  });
}
export function relayedOrOne(xs: number[]): number[] {
  return xs.map((x: number): number => {
    try {
      return relayed(x);
    } catch {
      return 1;
    }
  });
}
// `Math.max` states the empty footprint on normal return only: a caller of it
// states none on a throw.
export function largest(a: number, b: number): number {
  return Math.max(a, b);
}
