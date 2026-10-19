// A global declaration merging a `label` into the standard library's `Iterator`, as another module of a
// project may declare it. Merging installs no runtime member; it changes
// what every value of the type is stated to hold.
declare global {
  interface Iterator<T, TReturn, TNext> {
    label(): string;
  }
}
export {};
