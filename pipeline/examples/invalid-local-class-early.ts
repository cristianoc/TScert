// A closure created before a class its block declares reads the class:
// called before the class statement runs, it throws a ReferenceError (run
// under Node), where the class's binding is uninitialized.
export function early(): object {
  const make = (): object => new Late();
  const made = make();
  class Late {}
  return made;
}
