// A mutable tuple's `length` is not its arity: a push lengthens it, so a view
// of `length` at the arity reads a different number.
export function tupleLength(seed: number): 1 {
  const pair: [number] = [seed];
  const view: { readonly length: 1 } = pair;
  pair.push(seed);
  return view.length;
}
