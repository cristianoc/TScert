// A global declaration restating `ReadonlyArray`'s `at` exactly as the
// standard library and the overlay spell it.
declare global {
  interface ReadonlyArray<T> {
    at(index: number): T | undefined;
  }
}
export {};
