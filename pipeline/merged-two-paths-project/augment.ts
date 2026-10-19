// A global declaration giving `ReadonlyArray` one generic base along two
// heritage paths at different arguments: `Box<T>`'s `at` is the reviewed one,
// `Box<string>`'s is not.
declare global {
  interface Box<U> {
    at(index: number): U | undefined;
  }
  interface Left<T> extends Box<T> {}
  interface Right<T> extends Box<string> {}
  interface ReadonlyArray<T> extends Left<T>, Right<T> {}
}
export {};
