// A class declared in a block whose name another declaration of the file
// binds: the class's type is read under its name.
export function first(): object {
  class Shared {}
  return new Shared();
}

export function second(): number {
  const Shared = 1;
  return Shared;
}
