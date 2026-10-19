// The copy of a bounded binder's value is not a value of the binder: it takes
// the operand's own enumerable properties, and a class instance's getter is
// on its prototype (run under Node: `relabel(new (class { name = "a"; get
// size() { return 1; } })()).size` is undefined).
export function relabel<B extends { name: string; size: number }>(b: B): B {
  return { ...b, name: "x" };
}
