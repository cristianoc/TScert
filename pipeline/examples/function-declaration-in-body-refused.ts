// A function declaration in a body is created when its block is entered,
// so `f()` runs before `x` is initialized and throws (run under Node); the
// fragment has no function declarations in bodies, refused at it.
export function early(): number {
  const r = f();
  const x: number = 1;
  function f(): number {
    return x;
  }
  return r;
}
