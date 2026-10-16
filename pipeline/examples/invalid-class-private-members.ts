// A private slot is a key no object literal spells: a literal with the
// class's public members is no instance of it (TypeScript rejects the call
// too), and reading `#count` of it would read nothing.
class Counter {
  #count: number = 0;
  count(): number {
    return this.#count;
  }
}

function read(c: Counter): number {
  return c.count();
}

export function forged(): number {
  // @ts-expect-error the literal lacks the private slot
  return read({ count: () => 1 });
}
