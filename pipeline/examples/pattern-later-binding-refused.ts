// A default reading a binding its own declaration initializes later throws
// in JavaScript (the temporal dead zone); the lowering would read the outer
// binding of that name instead.
const later: number = 1;
export function laterBinding(source: {
  first?: number;
  later?: number;
}): number {
  const { first = later, later = 2 } = source;
  return first;
}
