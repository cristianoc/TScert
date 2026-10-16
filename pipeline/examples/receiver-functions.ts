"use strict";
// A module function's leading `this: T` parameter is its receiver, not a
// position: `.call`, `.apply` and `.bind` pass it, and a plain call passes
// `undefined`, which `this: void` admits. `.apply` with an array literal is
// the `.call` with its elements.
interface Ctx {
  value: number;
}
function withThis(this: Ctx, x: number): number {
  return this.value + x;
}
function noThis(this: void, x: number): number {
  return x;
}
function optional(this: Ctx, a: number, b?: string): number {
  return a;
}
function callIt(ctx: Ctx): number {
  return withThis.call(ctx, 1);
}
function applyIt(ctx: Ctx): number {
  return withThis.apply(ctx, [2]);
}
function bindIt(ctx: Ctx): number {
  const bound: (x: number) => number = withThis.bind(ctx);
  return bound(3);
}
function plainCall(): number {
  return noThis(4);
}
function anyReceiver(ctx: Ctx): number {
  return noThis.call(ctx, 5);
}
function omitted(ctx: Ctx): number {
  return optional.call(ctx, 6);
}
