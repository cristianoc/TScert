// A module replacing its class's prototype by an object holding a
// `[Symbol.hasInstance]` method, which answers `instanceof` of the class
// (`invalid-instanceof-hooked-value-import`, run under Node).
export class Hooked {
  readonly n: number = 1;
}

Object.setPrototypeOf(Hooked, {
  [Symbol.hasInstance](_: unknown): boolean {
    return true;
  },
});
