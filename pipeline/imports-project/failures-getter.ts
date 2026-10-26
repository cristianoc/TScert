// A module defining, through an alias of its class, a getter for the class
// value's `[Symbol.hasInstance]` that returns the standard method and pops
// an array (`invalid-instanceof-getter-value-import`, run under Node).
export class Getter {
  readonly g: number = 1;
}

export const saved: number[] = [1, 2];

const alias = Getter;
Object.defineProperty(alias, Symbol.hasInstance, {
  get(): unknown {
    saved.pop();
    return Function.prototype[Symbol.hasInstance];
  },
});
