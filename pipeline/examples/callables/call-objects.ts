"use strict";
/**
 * An object holds both an ordinary method and an arrow. Extracting the method
 * and using .call supplies a different receiver; .call on the arrow preserves
 * its lexical capture. The result is true for either seed.
 *
 * The directive makes the code strict, the receiver rule the verifier models.
 * The OCaml producer's claims verify. `.call` is
 * the intrinsic here because `owner` is a `const` object literal and nothing
 * in the file writes `choose` or `read`.
 */
function callObjects(seed: boolean): boolean {
  const owner = {
    value: seed,
    choose(this: { value: boolean }, first: boolean, second: boolean): boolean {
      return this.value ? first : second;
    },
    read: (): boolean => seed,
  };
  const receiver: { value: boolean } = { value: !seed };
  const method = owner.choose;
  const rebound: boolean = method.call(receiver, true, false);
  const lexical: boolean = owner.read.call(receiver);
  return rebound ? !lexical : lexical;
}
