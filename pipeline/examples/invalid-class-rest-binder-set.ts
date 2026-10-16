class RestRunner<T extends readonly unknown[]> {
  args: T;
  callback: (...args: T) => number;
  constructor(args: T, callback: (...args: T) => number) {
    this.args = args;
    this.callback = callback;
  }
  set(args: T): void {
    this.args = args;
  }
  run(): number {
    return this.callback(...this.args);
  }
}

// `set` stores an array shorter than the callback's parameters: `run` passes
// no actual for `x`, which is then `undefined`, and `toFixed` throws.
function lose(seed: number): number {
  const runner = new RestRunner(
    [seed] as const,
    (x: number): number => x.toFixed().length,
  );
  // @ts-expect-error The stored array is no `readonly [number]`.
  runner.set([] as const);
  return runner.run();
}

export const lost = lose(1);
