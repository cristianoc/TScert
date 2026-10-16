// A direct `eval` runs its string in the caller's scope: here it gives the
// local `g` an own `call` property, which `g.call` then runs.
function probe(): number {
  const g = (): number => 1;
  eval('g.call = () => "wrong"');
  return g.call(undefined);
}
