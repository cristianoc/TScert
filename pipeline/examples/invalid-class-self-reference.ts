// A static initializer runs while the class is being defined, before the
// module's binding of the class holds it: `make` reads that binding, so the
// call throws. Inside the class its own name is bound already; a module
// function's is not.
class Counter {
  n: number;
  constructor(n: number) {
    this.n = n;
  }
  static readonly first: number = make();
}
function make(): number {
  return new Counter(1).n;
}
