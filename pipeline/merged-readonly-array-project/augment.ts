// A global declaration merging a `toJSON` into the standard library's
// `ReadonlyArray`, as another module of a project may declare it. Merging
// installs no runtime hook; it changes what every read-only array annotation
// states.
declare global {
  interface ReadonlyArray<T> {
    toJSON(): undefined;
  }
}
export {};
