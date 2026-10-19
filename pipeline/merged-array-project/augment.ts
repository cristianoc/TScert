// A global declaration merging a `toJSON` into the standard library's
// `Array`, as another module of a project may declare it. Merging installs no
// runtime hook; it changes what every array annotation states.
declare global {
  interface Array<T> {
    toJSON(): undefined;
  }
}
export {};
