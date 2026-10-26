// A module defining its class's `[Symbol.hasInstance]` in its default
// export's expression (`invalid-instanceof-default-hook-value-import`, run
// under Node).
export class DefaultHooked {
  readonly n: number = 1;
}

export default Object.defineProperty(DefaultHooked, Symbol.hasInstance, {
  value: (_: unknown): boolean => true,
});
