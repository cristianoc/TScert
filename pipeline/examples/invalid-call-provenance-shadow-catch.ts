// The caught `g` is what the caller threw, not the local arrow of the same
// name: a function that may own a `call` property returning a string.
function probe(h: () => void): number {
  const g = (): number => 1;
  try {
    h();
  } catch (g) {
    return (g as () => number).call(undefined);
  }
  return g.call(undefined);
}
