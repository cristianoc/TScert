// A private name `#x` is a key of its own, which no code outside its class
// spells: a private field is an own key of each instance, a private method
// its prototype's, and a static one a binding as any static is. A spread
// copies no private slot.
class Counter {
  #count: number = 0;
  #label: string;
  static #twice(n: number): number {
    return n * 2;
  }
  static readonly #step: number = 1;
  static readonly start: number = Counter.#twice(Counter.#step);
  constructor(label: string) {
    this.#label = label;
  }
  #bump(by: number): number {
    this.#count = this.#count + by;
    return this.#count;
  }
  next(): number {
    this.#count = this.#count + 1;
    return this.#bump(2);
  }
  label(): string {
    return this.#label;
  }
  same(other: Counter): boolean {
    return other.#count === this.#count;
  }
}

export function use(c: Counter): number {
  return c.next() + c.label().length + Counter.start;
}

export function spread(c: Counter): { n: number } {
  const copy = { ...c, n: 1 };
  return copy;
}
