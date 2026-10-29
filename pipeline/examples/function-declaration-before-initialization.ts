// A function declaration in a body is created when its block is entered,
// so `f()` runs before `x` is initialized and throws (run under Node: a
// ReferenceError); `x` is an early binding, its read in `f` a checked access.
export function early(): number {
  const r = f();
  const x: number = 1;
  function f(): number {
    return x;
  }
  return r;
}

// A closure created above `x` mentions `f`, which is bound before it: the
// call through the closure, before `x` is initialized, throws too (run under
// Node: a ReferenceError).
export function throughClosure(): number {
  const get = (): number => f();
  const r = get();
  const x: number = 1;
  function f(): number {
    return x;
  }
  return r;
}
