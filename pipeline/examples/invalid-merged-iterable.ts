// Another module of the project adds a required `label` to `Iterable`. A
// named `Iterable<number>` is read at its merged declarations, `label`
// included, which an array does not hold: the return is refused (TypeScript
// refuses it too).
export function asIterable(xs: number[]): Iterable<number> {
  return xs;
}
