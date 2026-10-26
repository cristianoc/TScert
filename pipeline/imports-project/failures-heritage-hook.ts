// A module defining its class's `[Symbol.hasInstance]` in another class's
// heritage clause (`invalid-instanceof-heritage-hook-value-import`, run
// under Node).
export class BaseHooked {
  readonly n: number = 1;
}

export class Derived extends (Object.defineProperty(
  BaseHooked,
  Symbol.hasInstance,
  {
    value: (_: unknown): boolean => true,
  },
),
BaseHooked) {}
