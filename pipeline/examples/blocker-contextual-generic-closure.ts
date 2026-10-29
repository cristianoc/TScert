// Closures written without type parameters, at fields whose type is a
// generic signature: TypeScript types their parameters at that signature's
// type parameter R, which each closure then binds as its own. An arrow and
// a function expression, each checked at its binder and then at the
// signature its field states.
// Census functions:
// declaration-graph.mts#collectDeclarations.
type Reader = <R>(body: string, read: (text: string) => R) => R;
interface Library {
  reviewed: Reader;
  other: Reader;
}
export function lengthOf(text: string): number {
  const library: Library = {
    reviewed: (body, read) => read(body),
    other: function (body, read) {
      return read(body.trim());
    },
  };
  return library.reviewed(text, t => t.length) + library.other(text, t => t.length);
}
