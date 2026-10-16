// A class binder typing a field and a callback's rest: `run` spreads the
// stored array into the callback, whose parameters are the array's elements.
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

function keep(seed: number): number {
  const runner = new RestRunner(
    [seed, 2] as const,
    (x: number, y: number): number => x * 10 + y,
  );
  runner.set([seed + 1, 2] as const);
  return runner.run();
}

function pair(): number {
  const runner = new RestRunner<[string, number]>(
    ["ab", 5],
    (s: string, n: number): number => s.length + n,
  );
  return runner.run();
}

export const kept = keep(4);
export const paired = pair();
