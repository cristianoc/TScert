// A generic declaration's function types at an instance, read through the
// signature TypeScript instantiates: an assertion's promise about its
// parameter, which narrows the asserted value, and a stated receiver, kept
// where the closure passes its parameter on.
interface Check<T> {
  run(assert: (v: unknown) => asserts v is T): T;
  bound(cb: (this: T, n: number) => number): number;
}

function assertString(v: unknown): asserts v is string {
  if (typeof v !== "string") throw new Error("not a string");
}

function width(this: string, n: number): number {
  return this.length + n;
}

function held(cb: (this: string, n: number) => number): number {
  const box = { cb };
  return box.cb === width ? 1 : 0;
}

function useCheck(check: Check<string>): string {
  return check.run(assertString) + check.bound(width);
}

export function runCheck(): string {
  return useCheck({
    run(assert) {
      const v: unknown = "value";
      assert(v);
      return v;
    },
    bound(cb) {
      return held(cb);
    },
  });
}
