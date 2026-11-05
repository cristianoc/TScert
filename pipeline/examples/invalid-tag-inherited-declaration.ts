// An interface inheriting `Symbol.toStringTag` from `Map` and stating the
// native `then`, `catch` and `finally`, a value of it returned as a
// `Promise<number>`: refused first at the covering rule for the methods'
// binders. Its tag is a field of the instance, not of the prototype the
// native `Promise` contract requires; the forged documents of
// pipeline/test.mts state such a prototype and are refused.
interface Fake extends Map<string, number> {
  then<A = number, B = never>(
    onfulfilled?: ((value: number) => A | PromiseLike<A>) | null,
    onrejected?: ((reason: unknown) => B | PromiseLike<B>) | null,
  ): Promise<A | B>;
  catch<B = never>(
    onrejected?: ((reason: unknown) => B | PromiseLike<B>) | null,
  ): Promise<number | B>;
  finally(onfinally?: (() => void) | null): Promise<number>;
}

export function forged(f: Fake): Promise<number> {
  return f;
}
