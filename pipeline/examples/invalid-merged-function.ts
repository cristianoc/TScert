// Another module of the project merges `toJSON(): undefined` into
// `Function`, stating a member of every function: the unit is refused at its
// first construct reaching the declarations, here the global `Math`.
export function apply(f: (x: number) => number): number {
  return f(Math.abs(-1));
}
