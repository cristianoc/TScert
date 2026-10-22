// One host's `next` is an accessor: GetIterator's read of `next` runs the
// getter, which clears a field the function tested before the loop, so the
// test's narrowing does not survive the read (tests/node-runs.mts runs
// `kept`, which returns `undefined` despite its number contract).
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

class Lazy {
  readonly box: Box;
  constructor(box: Box) {
    this.box = box;
  }
  get next(): () => IteratorResult<number, undefined> {
    this.box.v = undefined;
    return () => ({ done: true, value: undefined });
  }
  return(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
  [Symbol.iterator](): Lazy {
    return this;
  }
}

export function kept(it: Countdown | Lazy, box: Box): number {
  if (box.v === undefined) return 0;
  for (const x of it) if (x > 0) break;
  return box.v;
}
