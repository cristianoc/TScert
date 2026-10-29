// A closure at a generic signature whose parameter is itself a generic
// function type naming the signature's type parameter: the parameter's
// contextual type is a callable with type parameters.
type Folder = <R>(start: R, step: <S>(item: S, acc: R) => R) => R;
interface Library {
  fold: Folder;
}
export function folded(n: number): number {
  const library: Library = { fold: (start, step) => step("x", start) };
  return library.fold(n, (_item, acc) => acc);
}
