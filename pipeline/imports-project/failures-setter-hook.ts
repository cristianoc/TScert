// A module assigning to its class's static setter, which defines the
// class's `[Symbol.hasInstance]` (`invalid-instanceof-setter-hook-value-import`,
// run under Node).
export class SetterHooked {
  readonly n: number = 1;
  static set hook(f: (x: unknown) => boolean) {
    Object.defineProperty(this, Symbol.hasInstance, { value: f });
  }
}

SetterHooked.hook = (_: unknown): boolean => true;
