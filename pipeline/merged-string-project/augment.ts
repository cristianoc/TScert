// A global declaration merging a `shout` into the standard library's `String`, as another module of a
// project may declare it. Merging installs no runtime member; it changes
// what every value of the type is stated to hold.
declare global {
  interface String {
    shout(): string;
  }
}
export {};
