// `void e` evaluates `e` and yields undefined; `a, b` evaluates `a` for its
// effects and yields `b`.
function discard(f: () => number): undefined {
  return void f();
}
function statement(f: () => number): number {
  void f();
  const nothing: undefined = void 0;
  return nothing === undefined ? 1 : 2;
}
function twice(x: number): undefined {
  return void void x;
}
function voidPlusOne(f: () => number): number {
  return (f(), 1) + 1;
}
function sequence(o: { n: number }): number {
  return (o.n = 2), o.n;
}
