"use strict";
/*
 * Function.prototype.apply. The target, the receiver and the list are
 * evaluated first; then the list's length and each index are read, in order,
 * and the target is called with those elements. The list is read as an
 * array-like, never iterated. tests/apply.mts runs each function against the
 * value another order or another preparation would give.
 */

/** The receiver expression writes the list's first element before the list
 * is read: the target receives the written value. */
function orderedReads(seed: boolean): boolean {
  const list: [boolean, boolean] = [seed, seed];
  const first = (a: boolean, b: boolean): boolean => a;
  return first.apply((list[0] = !seed), list);
}

/** `.apply` passes its receiver to an ordinary function, and the list's
 * elements as the actuals. */
function applyReceiver(seed: boolean): boolean {
  const owner = { value: seed };
  const read = function (this: { value: boolean }, flip: boolean): boolean {
    return flip ? !this.value : this.value;
  };
  const list: [boolean] = [!seed];
  return read.apply(owner, list);
}

/** Without a list there are no actuals. */
function applyNothing(seed: boolean): boolean {
  const owner = { value: seed };
  const read = function (this: { value: boolean }): boolean {
    return this.value;
  };
  return read.apply(owner);
}

/** A list of any length goes to a target taking only a rest parameter: its
 * positions are the actuals, `undefined` at a hole, so the element contract
 * admits it. */
function applyAnyLength(seed: boolean, list: (boolean | undefined)[]): boolean {
  const owner = { value: seed };
  const count = function (
    this: { value: boolean },
    ...rest: (boolean | undefined)[]
  ): boolean {
    return this.value;
  };
  return count.apply(owner, list);
}
