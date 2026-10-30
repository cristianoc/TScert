// Augmentations of the standard library, as another module of a project may
// declare them: `ObjectConstructor` with an `assign` of its own, and `Boolean`
// with an optional method.
declare global {
  interface ObjectConstructor {
    assign(n: number): string;
  }
  interface Boolean {
    probe?(): number;
  }
}
export {};
