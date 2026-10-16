// A static method's receiver is whatever its call passes: `Holder` for
// `Holder.read()`, `undefined` detached, where `this.base` throws.
// (TypeScript accepts this.) A static method reading `this` is outside the
// fragment.
class Holder {
  static readonly base: number = 1;
  static read(): number {
    return this.base;
  }
}
export function detached(): number {
  const read = Holder.read;
  return read();
}
