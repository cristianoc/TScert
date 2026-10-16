// A derived instance is its base's part, copied, then its own fields: a
// copy holds no private slot, so a class with a private name takes no part
// in inheritance.
class Base {
  #secret: number = 1;
  reveal(): number {
    return this.#secret;
  }
}
class Derived extends Base {
  extra: number = 2;
}

export function make(): Derived {
  return new Derived();
}
