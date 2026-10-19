// A set is within a target only if every element is: 3 is no `1 | 2`.
export function narrow(x: 1 | 2 | 3): 1 | 2 {
  return x;
}
