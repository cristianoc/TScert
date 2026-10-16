// An async method is a method returning its promise: its body awaits and
// returns through the intrinsic steps an async function's does, and it is
// called and awaited as any method.
declare function fetchCount(key: string): Promise<number>;

class Counter {
  base: number;
  constructor(base: number) {
    this.base = base;
  }
  async next(key: string): Promise<number> {
    const n = await fetchCount(key);
    return n + this.base;
  }
  async done(): Promise<void> {
    await this.next("done");
  }
  static async zero(): Promise<number> {
    return 0;
  }
}

export async function use(c: Counter): Promise<number> {
  const a = await c.next("a");
  await c.done();
  return a + (await Counter.zero());
}
