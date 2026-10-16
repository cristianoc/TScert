// A call instantiates a rest's argument pack at the list it collects, which
// must be within the parameter's bound: a string is no number.
function total<T extends readonly number[]>(...args: T): number {
  let sum = 0;
  for (const n of args) sum += n;
  return sum;
}

export function wrong(): number {
  // @ts-expect-error: a string is no number
  return total(1, "2");
}
