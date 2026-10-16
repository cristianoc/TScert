class RestRunner<T extends readonly unknown[]> {
  args: T;
  callback: (...args: T) => number;
  constructor(args: T, callback: (...args: T) => number) {
    this.args = args;
    this.callback = callback;
  }
  run(): number {
    return this.callback(...this.args);
  }
}

type Tagged = number[] & { tag: string };

// A binder typing a rest ranges over plain array and tuple types: the array a
// call collects is fresh, with the elements and none of a tagged array's
// other members, so it is no `Tagged`. The instance is refused here.
export function tagged(value: Tagged): number {
  const runner = new RestRunner<Tagged>(value, (x: number): number => x);
  return runner.run();
}
