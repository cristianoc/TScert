"use strict";
// `.call` passes its first argument as the receiver, which must meet the
// function's `this` parameter: a receiver without `value` reads undefined.
interface Ctx {
  value: number;
}
function withThis(this: Ctx, x: number): number {
  return this.value + x;
}
function wrongReceiver(other: { other: number }): number {
  // @ts-expect-error the receiver is not a Ctx
  return withThis.call(other, 1);
}
