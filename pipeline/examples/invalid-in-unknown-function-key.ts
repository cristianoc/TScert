// `typeof x === "function"` leaves a class, whose static members the model
// binds apart from it, and a function, which owns `name`, a key the model's
// function lacks: the test is refused. Under Node, `probe(() => 0)` returns
// true.
export function probe(x: unknown): boolean {
  return typeof x === "function" && "name" in x;
}
