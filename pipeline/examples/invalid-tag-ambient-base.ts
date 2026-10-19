// A class extending a declared class that states `Symbol.toStringTag`
// beside `then`, `catch` and `finally`: its instance's prototype is the
// class's own, which holds no tag, and a declared class's tag is an own
// field, so the instance asserted to be a `Promise<number>` is refused.
declare class Base {
  readonly [Symbol.toStringTag]: string;
  then(onfulfilled?: (value: number) => unknown): Promise<unknown>;
  catch(onrejected?: (reason: unknown) => unknown): Promise<unknown>;
  finally(onfinally?: () => void): Promise<number>;
}
class Derived extends Base {}

export function forged(d: Derived): Promise<number> {
  return d as unknown as Promise<number>;
}
