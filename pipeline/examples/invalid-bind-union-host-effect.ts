// One host's `next` clears a field the function tested before the loop:
// the bound `next` may change every location, so the test's narrowing does
// not survive the step (tests/node-runs.mts runs `kept`, which returns
// `undefined` despite its number contract).
class Box {
  v: number | undefined;
  constructor(v: number | undefined) {
    this.v = v;
  }
}

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
  return(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
  [Symbol.iterator](): Countdown {
    return this;
  }
}

class Drain {
  readonly box: Box;
  constructor(box: Box) {
    this.box = box;
  }
  next(): IteratorResult<number, undefined> {
    this.box.v = undefined;
    return { done: true, value: undefined };
  }
  return(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
  [Symbol.iterator](): Drain {
    return this;
  }
}

export function kept(it: Countdown | Drain, box: Box): number {
  if (box.v === undefined) return 0;
  for (const x of it) if (x > 0) break;
  return box.v;
}
