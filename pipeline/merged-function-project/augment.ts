// A global declaration merging a `toJSON` into the standard library's `Function`, as another module of a
// project may declare it. Merging installs no runtime member; it changes
// what every value of the type is stated to hold.
declare global {
  interface Function {
    toJSON(): undefined;
  }
}
export {};
