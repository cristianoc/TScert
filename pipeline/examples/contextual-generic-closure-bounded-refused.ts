// A closure at a generic signature whose type parameter is bounded: the
// closure would take R with its bound, which its scheme does not state.
type Reader = <R extends string>(body: string, read: (text: string) => R) => R;
interface Library {
  reviewed: Reader;
}
export function nameOf(text: string): string {
  const library: Library = { reviewed: (body, read) => read(body) };
  return library.reviewed(text, t => t);
}
