// A global declaration merging the standard library's own `at` into `ReadonlyArray`, at another binder and parameter name.
declare global {
  interface ReadonlyArray<U> {
    at(position: number): U | undefined;
  }
}
export {};
