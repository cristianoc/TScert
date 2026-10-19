// A global declaration merging a `label` into the standard library's `ArrayIterator`, as another module of a
// project may declare it. Merging installs no runtime member; it changes
// what every value of the type is stated to hold.
declare global {
  interface ArrayIterator<T> {
    label(): string;
  }
}
export {};
