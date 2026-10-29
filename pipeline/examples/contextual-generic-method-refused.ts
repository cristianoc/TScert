// A method of an object literal at a generic signature: TypeScript types
// its parameters at the signature's type parameter R, and the type it
// states for the method's declaration does not bind R.
type Reader = <R>(body: string, read: (text: string) => R) => R;
interface Library {
  reviewed: Reader;
}
export function lengthOf(text: string): number {
  const library: Library = {
    reviewed(body, read) {
      return read(body);
    },
  };
  return library.reviewed(text, t => t.length);
}
