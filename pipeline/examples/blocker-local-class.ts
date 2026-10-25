// A class declared inside a function needs local class lowering.
// Census functions:
// array-prototype.mts#arrayPrototype, array-prototype.mts#mergeRefusal,
// array-prototype.mts#primitivePrototype, array-prototype.mts#prototype.
export function use(): void {
  class Unread extends Error {}
}
