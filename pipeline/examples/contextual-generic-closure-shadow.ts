// A closure at a generic signature whose type parameter R is spelled as a
// type parameter of the enclosing function: the closure binds its own R
// under a fresh name, and a type its body writes, `R`, is the outer one.
type Reader = <R>(body: string, read: (text: string) => R) => R;
interface Library {
  reviewed: Reader;
}
export function lengthOf<R>(text: string, other: R): R {
  const library: Library = {
    reviewed: (body, read) => {
      const kept: R = other;
      return read(body);
    },
  };
  library.reviewed(text, t => t.length);
  return other;
}
