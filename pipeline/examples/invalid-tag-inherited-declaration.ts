// An interface inheriting `Symbol.toStringTag` from `Map` and stating the
// native `then`, `catch` and `finally`: a tag a declaration inherits is a
// field of the instance, not of the prototype the native `Promise` contract
// requires, so a value of it returned as a `Promise<number>` is refused.
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
