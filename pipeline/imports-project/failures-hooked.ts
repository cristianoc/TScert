// A module replacing its class value's prototype by an object holding a
// `[Symbol.hasInstance]` method, which answers `instanceof` of the class,
// through an element access and a parenthesized argument
// (`invalid-instanceof-hooked-value-import`, run under Node).
export class Hooked {
  readonly n: number = 1;
}

// prettier-ignore
Object["setPrototypeOf"]((Hooked), {
  [Symbol.hasInstance](_: unknown): boolean {
    return true;
  },
});
