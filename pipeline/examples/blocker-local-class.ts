// A class declared inside a function, constructed and thrown by a closure
// and caught at `instanceof`.
// Census functions:
// array-prototype.mts#arrayPrototype, array-prototype.mts#mergeRefusal,
// array-prototype.mts#primitivePrototype, array-prototype.mts#prototype.
export function use(read: (fail: (message: string) => never) => string): string | null {
  class Unread extends Error {}
  const fail = (message: string): never => {
    throw new Unread(message);
  };
  try {
    return read(fail);
  } catch (error) {
    if (error instanceof Unread) return null;
    throw error;
  }
}
