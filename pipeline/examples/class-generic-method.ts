// A class's generic methods: the instance's members with quantified
// signatures, which its prototype's closures, schemes received by the
// instance and binding the same rows, cover. A method reading `this`, and
// calls at two instances.
class Helper {
  base: number = 1;
  pick<V>(a: V): V {
    return a;
  }
  run<U>(f: (n: number) => U): U {
    return f(this.base);
  }
}
export function use(h: Helper): number {
  return h.pick(1);
}
export function both(h: Helper): string {
  const n: number = h.run((x: number) => x + 1);
  const s: string = h.pick("a");
  return n > 0 ? s : "";
}
export function make(): Helper {
  return new Helper();
}
