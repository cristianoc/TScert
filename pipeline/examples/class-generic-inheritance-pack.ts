class CallbackBase<Args extends readonly unknown[]> {
  constructor(
    public values: Args,
    public callback: (...args: Args) => number,
  ) {}
}

class TupleCallback extends CallbackBase<[number, string]> {}

export function callTuple(
  values: [number, string],
  callback: (n: number, text: string) => number,
): number {
  const pair = new TupleCallback(values, callback);
  return pair.callback(pair.values[0], "hello");
}

class ArrayCallback extends CallbackBase<number[]> {}

export function callArray(
  values: number[],
  callback: (...args: number[]) => number,
): number {
  return new ArrayCallback(values, callback).callback(1, 2);
}

class Other<Args extends readonly unknown[]> {
  constructor(values: Args, callback: (...args: Args) => number) {
    callback(...values);
  }
}
