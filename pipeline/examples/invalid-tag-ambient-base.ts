// A class extending a declared class that states `Symbol.toStringTag`
// beside `then`, `catch` and `finally`, its instance asserted to be a
// `Promise<number>`: refused at the base, since a class extends only a class
// of its file, which keeps every prototype of an object the program makes
// free of the tag.
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
