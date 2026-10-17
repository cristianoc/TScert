// An augmentation of the standard library's `ObjectConstructor` with an
// `assign` of its own, as another module of a project may declare it.
declare global {
  interface ObjectConstructor {
    assign(n: number): string;
  }
}
export {};
