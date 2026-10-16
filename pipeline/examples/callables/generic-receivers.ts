"use strict";
/*
 * One quantified ordinary function, instantiated at two receiver contracts.
 * Its receiver type is a binder; the cell it captures keeps its one fixed
 * contract at every instantiation. tests/generic-receivers.mts checks both.
 */

/** Each call gives back the receiver it passed, at that receiver's type.
 * TypeScript's `.call` forgets the binder and types the result `unknown`; each
 * cast is an obligation the verifier checks against the instantiated result. */
function genericSelf(seed: boolean): boolean {
  const self = function <R>(this: R): R {
    return this;
  };
  const a = { value: seed };
  const b = { flag: !seed };
  const first = self.call(a) as { value: boolean };
  const second = self.call(b) as { flag: boolean };
  return first.value ? !second.flag : seed;
}

/** A captured cell read at two receiver instantiations sees one contract and
 * the live contents. */
function genericCapture(seed: boolean): boolean {
  let store: boolean = seed;
  const read = function <R>(this: R): boolean {
    return store;
  };
  const a = { value: seed };
  const b = { flag: !seed };
  const x = read.call(a);
  store = !seed;
  const y = read.call(b);
  return x ? !y : y;
}
