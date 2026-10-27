// A `length` on `Uint8Array.prototype` shadows `%TypedArray%.prototype`'s
// getter for every view (run under Node: a view's `length` is a string):
// `Uint8Array` is outside the reviewed globals, refused.
export function shadow(value: string): void {
  Object.defineProperty(Uint8Array.prototype, "length", {
    configurable: true,
    value,
  });
}
