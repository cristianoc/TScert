// A pattern binding a `for...of` over an iterable the program defines: each
// step's value is bound, then destructured first in the protocol's closing
// region, before the body. A throw of the destructuring closes the iterator,
// as a throw out of the body does (tests/node-runs.mts runs these functions
// and reads the count of closes).
type Item = { name: string; size?: number };

class Link {
  readonly item: Item;
  readonly pair: [string, number];
  readonly next: Link | null;
  constructor(item: Item, pair: [string, number], next: Link | null) {
    this.item = item;
    this.pair = pair;
    this.next = next;
  }
}

class Items {
  readonly head: Link | null;
  readonly log: { closed: number };
  constructor(head: Link | null, log: { closed: number }) {
    this.head = head;
    this.log = log;
  }
  [Symbol.iterator](): Iterator<Item> {
    let node = this.head;
    const log = this.log;
    return {
      next: (): IteratorResult<Item> => {
        const current = node;
        if (current === null) return { done: true, value: undefined };
        node = current.next;
        return { done: false, value: current.item };
      },
      return: (): IteratorResult<Item> => {
        log.closed = log.closed + 1;
        return { done: true, value: undefined };
      },
    };
  }
}

class Pairs {
  readonly head: Link | null;
  constructor(head: Link | null) {
    this.head = head;
  }
  [Symbol.iterator](): Iterator<[string, number]> {
    let node = this.head;
    return {
      next: (): IteratorResult<[string, number]> => {
        const current = node;
        if (current === null) return { done: true, value: undefined };
        node = current.next;
        return { done: false, value: current.pair };
      },
      return: (): IteratorResult<[string, number]> => ({
        done: true,
        value: undefined,
      }),
    };
  }
}

// The form of `type-term.mts#quantified`: an array's `entries()`, an
// `ArrayIterator` of pairs the protocol steps, each pair destructured.
export function indexed(words: readonly string[]): string {
  let out = "";
  for (const [i, word] of words.entries()) out = `${out}${i}:${word} `;
  return out;
}

// `keys` and `values` give `ArrayIterator`s of the indices and the elements.
export function spelled(words: readonly string[]): string {
  let out = "";
  for (const i of words.keys()) out = `${out}${i}`;
  for (const word of words.values()) out = `${out}${word}`;
  return out;
}

// A tuple pattern, with a hole, over the program's own iterable.
export function total(pairs: Pairs): number {
  let sum = 0;
  for (const [, n] of pairs) sum = sum + n;
  return sum;
}

export function keyed(pairs: Pairs): string {
  let out = "";
  for (const [key, n] of pairs) out = `${out}${key}=${n};`;
  return out;
}

// An object pattern with a default and a renamed field; a `let` nothing
// assigns binds as a `const`.
export function sizes(items: Items): number {
  let sum = 0;
  for (let { name: label, size = label.length } of items) sum = sum + size;
  return sum;
}

// `break` after the destructuring: the iterator's `return` runs once.
export function firstSized(items: Items): string {
  let found = "";
  for (const { name, size } of items) {
    if (size !== undefined) {
      found = name;
      break;
    }
  }
  return found;
}

// A default that throws: the destructuring's abrupt completion closes the
// iterator, and the default's error is the one that leaves.
function missing(name: string): number {
  throw new Error(`no size for ${name}`);
}

export function strict(items: Items): unknown {
  try {
    let sum = 0;
    for (const { name, size = missing(name) } of items) sum = sum + size;
    return sum;
  } catch (e) {
    return e;
  }
}

// Closures capture each iteration's own bindings.
export function namers(items: Items): (() => string)[] {
  const out: (() => string)[] = [];
  for (const { name } of items) out.push(() => name);
  return out;
}
