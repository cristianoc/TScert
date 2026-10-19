// A global declaration merging an `at` into `ReadonlyArray` whose result leaves out `undefined`.
declare global {
  interface ReadonlyArray<T> {
    at(index: number): T;
  }
}
export {};
