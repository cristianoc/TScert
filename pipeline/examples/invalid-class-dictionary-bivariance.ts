// A class constructible at `never` is still compared by its instances.
// TypeScript compares method parameters both ways, so a class whose method
// takes only `true` passes as one whose method takes any boolean.
class Strict {
  check(flag: true): boolean {
    return flag;
  }
}

interface Checker {
  check(flag: boolean): boolean;
}

class Registry {
  readonly checks: {
    readonly [name: string]: new (params: never) => Checker;
  } = { strict: Strict };
}

export function make(): Registry {
  return new Registry();
}
