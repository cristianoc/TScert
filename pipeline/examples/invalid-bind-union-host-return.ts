// A done step's value is the host's return value: a string for `Repeat`.
// Read without testing `done`, the step's value is a number, `undefined`
// or a string, not the number the function returns (tests/node-runs.mts
// runs `peek`, which returns "finished").
class Countdown {
  left: number;
  constructor(left: number) {
    this.left = left;
  }
  next(): IteratorResult<number, undefined> {
    const n = this.left;
    if (n <= 0) return { done: true, value: undefined };
    this.left = n - 1;
    return { done: false, value: n };
  }
}

class Repeat {
  times: number;
  constructor(times: number) {
    this.times = times;
  }
  next(): IteratorResult<number, string> {
    const t = this.times;
    if (t <= 0) return { done: true, value: "finished" };
    this.times = t - 1;
    return { done: false, value: t };
  }
}

export function peek(it: Countdown | Repeat): number {
  const r = it.next();
  return r.value;
}
