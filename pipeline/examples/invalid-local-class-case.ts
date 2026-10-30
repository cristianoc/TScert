// A class declared in a `case` clause: its binding is the clause list's,
// which control may enter at a later clause, before the class statement runs.
export function picked(n: number): object | null {
  switch (n) {
    case 0:
      class Picked {}
      return new Picked();
    default:
      return null;
  }
}
